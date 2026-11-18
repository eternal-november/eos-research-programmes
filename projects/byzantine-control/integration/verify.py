"""Reproduce the integrated theory, retained packages and all declared proof dependencies.

Lean scanning deliberately accepts a restricted direct-declaration source style,
not arbitrary Lean metaprograms, raw strings, escaped identifiers or string macros.
Unsupported source syntax is rejected before compilation rather than ignored.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parent
ALLOW={"propext","Classical.choice","Quot.sound"}
def need(x,msg):
    if not x: raise RuntimeError(msg)
def run(args,input_text=None):
    result=subprocess.run(args,cwd=HERE,input=input_text,text=True,encoding="utf-8",
                          capture_output=True)
    need(result.returncode==0,"Failed "+repr(args)+"\n"+result.stdout+"\n"+result.stderr)
    need(not result.stderr.strip(),"Unexpected stderr: "+result.stderr)
    return result.stdout.replace("\r\n","\n").strip()
def normalized(path):
    return path.read_bytes().replace(b"\r\n",b"\n")
def fingerprints():
    paths=[p for p in HERE.iterdir() if p.is_file() and p.suffix in (".py",".lean",".md",".json")
           and p.name!="verification.json"]
    # Bind actual transitive sources, not only their older manifest files.
    for directory in (PROJECT,PROJECT/"handoff",PROJECT/"enforcement",PROJECT/"research"):
        paths += [p for p in directory.iterdir() if p.is_file()
                  and p.suffix in (".py",".lean",".md",".json",".ps1")]
    paths.append(PROJECT/"handoff/lean-toolchain")
    paths=list(set(paths))
    return {p.relative_to(PROJECT).as_posix():hashlib.sha256(normalized(p)).hexdigest()
            for p in sorted(paths)}
def lexical_code(text):
    """Blank comments and string/character literals, preserving offsets/newlines."""
    out=list(text); i=0; depth=0
    def blank(a,b):
        for j in range(a,b):
            if out[j] not in ("\n","\r"):out[j]=" "
    while i<len(text):
        if depth:
            if text.startswith("/-",i):blank(i,i+2);depth+=1;i+=2
            elif text.startswith("-/",i):blank(i,i+2);depth-=1;i+=2
            else:blank(i,i+1);i+=1
        elif text.startswith("/-",i):
            blank(i,i+2);depth=1;i+=2
        elif text.startswith("--",i):
            end=text.find("\n",i)
            if end<0:end=len(text)
            blank(i,end);i=end
        elif text[i] in "«»":
            raise RuntimeError("Escaped Lean identifiers are outside the verifier syntax contract")
        elif (i==0 or not (text[i-1].isalnum() or text[i-1] in "_'")) and re.match(r'r#*"',text[i:]):
            raise RuntimeError("Raw Lean strings are outside the verifier syntax contract")
        elif (i==0 or not (text[i-1].isalnum() or text[i-1] in "_'")) and re.match(r"[A-Za-z_][A-Za-z0-9_']*!\"",text[i:]):
            raise RuntimeError("String macros are outside the verifier syntax contract")
        elif text[i]=='"':
            start=i;i+=1;closed=False
            while i<len(text):
                if text[i]=="\\":i+=2
                elif text[i]=='"':i+=1;closed=True;break
                else:i+=1
            need(closed,"Unterminated Lean string")
            blank(start,min(i,len(text)))
        elif text[i]=="'" and (i==0 or not (text[i-1].isalnum() or text[i-1] in "_'")):
            match=re.match(r"'(?:\\.|[^'\\\r\n])'",text[i:])
            if match:blank(i,i+len(match.group()));i+=len(match.group())
            else:i+=1
        else:i+=1
    need(depth==0,"Unterminated Lean block comment")
    return "".join(out)

IDENT=r"[A-Za-z_][A-Za-z0-9_']*"
def inspect_source(text):
    code=lexical_code(text)
    need(not re.search(r"\b(?:axiom|constant)\b",code),"Custom axiom declaration")
    # This verifier intentionally supports direct declarations, not macros
    # that can synthesize additional declarations behind the inventory.
    need(not re.search(r"(?m)^\s*(?:private\s+|protected\s+|unsafe\s+)?(?:macro|elab|syntax|initialize|run_elab)\b",code),
         "Unsupported declaration-generating Lean syntax")
    names=[]
    for match in re.finditer(r"\b(?:theorem|lemma)\b",code):
        start=code.rfind("\n",0,match.start())+1
        need(not code[start:match.start()].strip(),"Unsupported theorem modifier or declaration syntax")
        tail=code[match.end():]
        name=re.match(r"[ \t]+("+IDENT+r")(?=\s|[({:])",tail)
        need(name is not None,"Unsupported theorem identifier/syntax")
        names.append(name.group(1))
    namespaces=[]
    for match in re.finditer(r"\bnamespace\b",code):
        start=code.rfind("\n",0,match.start())+1
        end=code.find("\n",match.end())
        if end<0:end=len(code)
        line=code[start:end]
        parsed=re.fullmatch(r"\s*namespace\s+("+IDENT+r"(?:\."+IDENT+r")*)\s*",line)
        need(parsed is not None,"Unsupported namespace syntax")
        namespaces.append(parsed.group(1))
    need(len(namespaces)==1,"Expected one explicit source namespace")
    need(names,"Proof module has no declarations")
    need(len(names)==len(set(names)),"Duplicate theorem declaration inventory")
    imports=[];body=list(text);offset=0
    for line in code.splitlines(keepends=True):
        if re.search(r"\bimport\b",line):
            parsed=re.fullmatch(r"\s*import[ \t]+([^\r\n]*?)[ \t\r\n]*",line)
            need(parsed is not None,"Unsupported import syntax")
            modules=parsed.group(1).split()
            need(modules and all(re.fullmatch(IDENT+r"(?:\."+IDENT+r")*",m) for m in modules),
                 "Unsupported import token")
            imports.extend(modules)
            start=line.index("import");end=parsed.end(1)
            for j in range(offset+start,offset+end):
                if body[j] not in ("\n","\r"):body[j]=" "
        offset+=len(line)
    return [namespaces[0]+"."+n for n in names],imports,"".join(body)

def theorem_names(text):
    return inspect_source(text)[0]

def reports(output):
    need("warning" not in output.lower() and "sorry" not in output.lower(),"Unexpected Lean diagnostic")
    # Lean may wrap an axiom list over several lines; parse complete records.
    matches=re.findall(r"'([A-Za-z_][A-Za-z0-9_'.]*)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",output,re.S)
    parsed={}
    for name,kind,body in matches:
        deps=[] if kind.startswith("does not") else sorted(x.strip() for x in body.split(",") if x.strip())
        need(set(deps)<=ALLOW,"Forbidden axiom dependency for "+name+": "+repr(deps))
        if name in parsed: need(parsed[name]==deps,"Inconsistent duplicate axiom report")
        parsed[name]=deps
    residue=re.sub(r"'([A-Za-z_][A-Za-z0-9_'.]*)' (does not depend on any axioms|depends on axioms:\s*\[[^\]]*\])","",output,flags=re.S).strip()
    need(not residue,"Unparsed Lean output: "+residue)
    return parsed
def proof_check(path,lean):
    text=path.read_text(encoding="utf-8")
    names=theorem_names(text)
    dependency_paths={name:PROJECT/"research"/(name+".lean")
                      for name in ("Execution","Evidence","Control","QuorumAlignment","Digital")}
    dependency_paths.update({name:HERE/(name+".lean") for name in ("CoreBridge","Structure")})
    active=set();finished=set();pieces=[]
    def include(source,label):
        need(label not in active,"Cyclic proof dependency "+label)
        if label in finished:return
        active.add(label)
        _,imports,body=inspect_source(source)
        for imported in imports:
            if imported=="Std":continue
            need(imported in dependency_paths,"Unreviewed proof dependency "+imported)
            include(dependency_paths[imported].read_text(encoding="utf-8"),imported)
        pieces.append(body)
        active.remove(label);finished.add(label)
    include(text,path.stem)
    text="import Std\n"+"\n".join(pieces)
    extra="\n".join("#print axioms "+n for n in names)
    parsed=reports(run([lean,"--stdin"],text+"\n"+extra+"\n"))
    need(all(n in parsed for n in names),"Missing axiom report")
    return {n:parsed[n] for n in names}
def verifier_regressions(lean):
    """Independent-review counterexamples plus positive syntax controls."""
    class Fixture:
        def __init__(self,source,stem="VerifierFixture"):
            self.source=source;self.stem=stem
        def read_text(self,encoding="utf-8"):
            return self.source
    positive="""import Std
/- theorem fake : False := hidden
   import NotARealModule
   /- private axiom nested : False -/
-/
namespace VerifierFixture
def note : String := "theorem fake and import Missing"
theorem okay : True := True.intro
  theorem okay' : True := True.intro
end VerifierFixture
"""
    result=proof_check(Fixture(positive),lean)
    need(set(result)=={"VerifierFixture.okay","VerifierFixture.okay'"},
         "Indented/prime theorem inventory or comment handling failed")
    invalid={
      "multiple_import_tokens":"import Std NotARealModule\nnamespace V\ntheorem okay : True := True.intro\nend V",
      "private_axiom_and_indented_theorem":"import Std\nnamespace V\nprivate axiom hidden : False\n  theorem missed : False := hidden\ntheorem okay : True := True.intro\nend V",
      "prime_false_theorem":"import Std\nnamespace V\nprivate axiom hidden : False\ntheorem okay : True := True.intro\ntheorem okay' : False := hidden\nend V",
      "unsupported_modifier":"import Std\nnamespace V\nprotected theorem okay : True := True.intro\nend V",
      "raw_string_delimiter_bypass": 'import Std\nnamespace V\ndef first : String := r#" " /- "#\nprivate axiom hidden : False\ntheorem missed : False := hidden\ndef second : String := r#" -/ " "#\ntheorem okay : True := True.intro\nend V',
      "escaped_identifier_delimiter_bypass": 'import Std\nnamespace V\ndef «/-» : Nat := 0\nprivate axiom hidden : False\ntheorem missed : False := hidden\ndef «-/» : Nat := 0\ntheorem okay : True := True.intro\nend V',
    }
    rejected=[]
    for name,source in invalid.items():
        try:proof_check(Fixture(source),lean)
        except RuntimeError:rejected.append(name)
        else:raise RuntimeError("Verifier accepted invalid fixture "+name)
    try:
        proof_check(Fixture("import CoreBridge\nnamespace V\ntheorem okay : True := True.intro\nend V","CoreBridge"),lean)
    except RuntimeError as error:
        need("Cyclic" in str(error),"Cycle fixture failed for wrong reason");rejected.append("dependency_cycle")
    else:raise RuntimeError("Dependency cycle was accepted")
    for name,output in (("forbidden_dependency","'V.bad' depends on axioms: [propext, hidden]"),
                        ("admission","'V.bad' depends on axioms: [sorryAx]")):
        try:reports(output)
        except RuntimeError:rejected.append(name)
        else:raise RuntimeError("Invalid dependency report accepted")
    wrapped=reports("'V.okay' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]")
    need(set(wrapped["V.okay"])==ALLOW,"Wrapped dependency list failed")
    return {"positive_indented_prime_and_comment_control":True,
            "rejected_false_pass_classes":rejected,"wrapped_axioms":True}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    g=ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--write",action="store_true");g.add_argument("--check",action="store_true")
    ap.add_argument("--lean",default=str(Path(os.environ["USERPROFILE"])/".elan/toolchains/leanprover--lean4---v4.33.0/bin/lean.exe"))
    a=ap.parse_args()
    need(not sys.flags.optimize and sys.version_info[:2]==(3,12),"Unoptimized Python3.12 required")
    before=fingerprints(); record=HERE/"verification.json"
    expected=json.loads(record.read_text(encoding="utf-8")) if a.check else None
    if expected:need(expected["sources_sha256_lf"]==before,"Inputs changed; review before refreshing")
    version=run([a.lean,"--version"]);need("version 4.33.0," in version,"Lean4.33.0 required")
    guards=verifier_regressions(a.lean)
    proofs={}
    for path in sorted(HERE.glob("*.lean")):
        print("Checking "+path.name,flush=True)
        proofs[path.name]=proof_check(path,a.lean)
    outputs={}
    scripts=("core_bridge.py","structure_model.py","enactment_model.py","exchange_model.py",
             "applications.py","alignment_model.py","hierarchy_model.py")
    for script in scripts:
        path=HERE/script;need(path.exists(),"Missing integrated artifact "+script)
        print("Reproducing "+script,flush=True)
        outputs[script]=run([sys.executable,"-B",str(path),"--check"])
    print("Reproducing retained enforcement package",flush=True)
    outputs["retained_enforcement"]=run([sys.executable,"-B",str(PROJECT/"enforcement/verify.py"),"--check","--lean",a.lean])
    print("Reproducing retained research and foundation package",flush=True)
    outputs["retained_research"]=run(["powershell.exe","-NoProfile","-ExecutionPolicy","Bypass","-File",
        str(PROJECT/"research/verify_program.ps1"),"-LeanExecutable",a.lean,"-PythonExecutable",sys.executable])
    need(before==fingerprints(),"Research inputs changed during verification")
    actual={"format":1,"verification_passed":True,"scope":"Encoded results and deterministic evidence; full-program adequacy requires the separate independent completion audit",
            "lean_version":version,"python_major_minor":list(sys.version_info[:2]),
            "sources_sha256_lf":before,"integration_axiom_dependencies":proofs,"verifier_guard_checks":guards,
            "integration_theorem_count":sum(len(x) for x in proofs.values()),
            "retained_research_foundation_theorem_count":129,"retained_enforcement_theorem_count":26,
            "executable_check_outputs":outputs}
    rendered=json.dumps(actual,indent=2,sort_keys=True)+"\n"
    if a.write:record.write_text(rendered,encoding="utf-8",newline="\n")
    else:need(actual==expected,"Verification evidence differs")
    print("PASS: integrated statements, all component evidence and both retained packages",flush=True)
if __name__=="__main__":main()
