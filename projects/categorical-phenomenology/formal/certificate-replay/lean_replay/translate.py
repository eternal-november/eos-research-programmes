#!/usr/bin/env python3
"""Translate stored list certificates step-for-step into Lean proof terms.

No theorem search, simp, imported list lemmas, or calls to the Python kernel.
Every recorded rewrite emits an explicitly typed equality witness, lifted at
its exact AST path by congrArg. Lean checks all emitted proof terms.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

class Rejected(ValueError):
    pass

AXIOMS = {
 'app_nil': (('app',('nil',),('v','Y')), ('v','Y')),
 'app_cons': (('app',('cons',('e','a'),('v','X')),('v','Y')), ('cons',('e','a'),('app',('v','X'),('v','Y')))),
 'rev_nil': (('rev',('nil',)), ('nil',)),
 'rev_cons': (('rev',('cons',('e','a'),('v','X'))), ('app',('rev',('v','X')),('cons',('e','a'),('nil',))))
}
HEADER = '''-- Generated mechanically from a stored certificate bundle. Do not hand-edit.
-- Only the recursive definitions and equality/induction primitives are used.
import Init
set_option autoImplicit false
set_option linter.unusedVariables false
universe u
namespace CertificateReplay
variable {α : Type u}
def app : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: app xs ys
def rev : List α → List α
  | [] => []
  | x :: xs => app (rev xs) (x :: [])
theorem app_nil (v_Y : List α) : app [] v_Y = v_Y := rfl
theorem app_cons (e_a : α) (v_X v_Y : List α) :
    app (e_a :: v_X) v_Y = e_a :: app v_X v_Y := rfl
theorem rev_nil : rev ([] : List α) = [] := rfl
theorem rev_cons (e_a : α) (v_X : List α) :
    rev (e_a :: v_X) = app (rev v_X) (e_a :: []) := rfl
'''

def name(s):
    if not isinstance(s,str) or not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',s):
        raise Rejected(f'Unsupported identifier: {s!r}')
    return s

def freeze(t):
    if not isinstance(t,(list,tuple)) or not t:
        raise Rejected('Malformed term')
    return tuple(freeze(x) if isinstance(x,(list,tuple)) else x for x in t)

def sort(t):
    f=t[0]
    if f in ('v','e') and len(t)==2:
        name(t[1]); return 'L' if f=='v' else 'E'
    if f=='nil' and len(t)==1: return 'L'
    if f=='cons' and len(t)==3 and sort(t[1])=='E' and sort(t[2])=='L': return 'L'
    if f=='app' and len(t)==3 and sort(t[1])==sort(t[2])=='L': return 'L'
    if f=='rev' and len(t)==2 and sort(t[1])=='L': return 'L'
    raise Rejected('Ill-typed term')

def variables(t):
    if t[0] in ('v','e'): return {t}
    return set().union(*(variables(a) for a in t[1:])) if len(t)>1 else set()

def subst(t,env):
    if t[0] in ('v','e'): return env.get(t,t)
    return (t[0],*(subst(a,env) for a in t[1:]))

def match(pattern, term, env, fixed):
    if pattern[0] in ('v','e'):
        if pattern in fixed: return pattern==term
        if sort(pattern)!=sort(term): return False
        if pattern in env: return env[pattern]==term
        env[pattern]=term; return True
    return pattern[0]==term[0] and len(pattern)==len(term) and all(match(a,b,env,fixed) for a,b in zip(pattern[1:],term[1:]))

def subterm(t,path):
    for i in path:
        if type(i) is not int or i<1 or i>=len(t) or t[0] in ('v','e'):
            raise Rejected('Invalid path')
        t=t[i]
    return t

def replace(t,path,v):
    if not path: return v
    i=path[0]
    return t[:i]+(replace(t[i],path[1:],v),)+t[i+1:]

def varname(v): return v[0]+'_'+name(v[1])
def render(t):
    f=t[0]
    if f in ('v','e'): return varname(t)
    if f=='nil': return '([] : List α)'
    if f=='cons': return f'(List.cons {render(t[1])} {render(t[2])})'
    if f=='app': return f'(app {render(t[1])} {render(t[2])})'
    if f=='rev': return f'(rev {render(t[1])})'
    if f=='hole': return 'replay_hole'
    raise Rejected('Unknown constructor')

def params(eq): return sorted(variables(eq[0])|variables(eq[1]))
def binders(vs): return ''.join(f' ({varname(v)} : {"List α" if v[0]=="v" else "α"})' for v in vs)

class Exporter:
    def __init__(self,bundle,source_sha):
        self.bundle=bundle
        self.lines=HEADER.splitlines()
        self.lines.insert(1, f'-- Source bundle SHA256: {source_sha}')
        self.audit={'source_sha256':source_sha,'method':'literal_certificate_replay','declarations':[],'steps':[]}
        self.rules={k:{'equation':v,'lean_name':k,'params':params(v),'fixed':set()} for k,v in AXIOMS.items()}
        self.used_names=set(self.rules)|{'IH'}
    def emit(self,s=''): self.lines.append(s)
    def chain(self,start,steps,rules,label,indent,entry,branch):
        t=start; proofs=[]
        for i,s in enumerate(steps):
            key=s['rule']; direction=s.get('direction',1)
            if key not in rules or type(direction) is not int or direction not in (1,-1):
                raise Rejected('Unknown rule or direction')
            rule=rules[key]; eq=rule['equation']; lhs,rhs=eq if direction==1 else eq[::-1]
            if not variables(rhs)<=variables(lhs): raise Rejected('Unbound replacement variable')
            path=s['path']; u=subterm(t,path); env={}
            if not match(lhs,u,env,rule['fixed']): raise Rejected(f'Rule {key} does not match at {path}')
            out=replace(t,path,subst(rhs,env))
            if sort(out)!='L': raise Rejected('Replacement changed sort')
            args=''.join(f' ({varname(v)} := {render(env.get(v,v))})' for v in rule['params'])
            alpha='' if key=='IH' else ' (α := α)'
            inner=f'({rule["lean_name"]}{alpha}{args})'
            if direction==-1: inner=f'(Eq.symm {inner})'
            context=render(replace(t,path,('hole',)))
            proof=inner if not path else f'(congrArg (fun (replay_hole : List α) => {context}) {inner})'
            local=f'{label}_{i:03d}'
            self.emit(indent+f'-- {key}, direction {direction}, AST path {path}')
            self.emit(indent+f'have {local} : {render(t)} = {render(out)} := {proof}')
            self.audit['steps'].append({'entry':entry,'branch':branch,'side':label,'index':i,'rule':key,'direction':direction,'path':path,'before':t,'after':out,'substitution':[{'variable':v,'term':value} for v,value in sorted(env.items())], 'lean_line':len(self.lines)})
            proofs.append(local); t=out
        proof=f'(Eq.refl {render(t)})'
        for p in reversed(proofs): proof=f'(Eq.trans {p} {proof})'
        return t,proof
    def branch(self,a,b,cert,rules,indent,entry,branch):
        l,lp=self.chain(a,cert['left'],rules,'left',indent,entry,branch)
        r,rp=self.chain(b,cert['right'],rules,'right',indent,entry,branch)
        if l!=r: raise Rejected('Normal forms differ')
        self.emit(indent+f'exact Eq.trans {lp} (Eq.symm {rp})')
    def entry(self,entry,library):
        nm=name(entry['name'])
        if library and nm in self.used_names: raise Rejected('Duplicate or reserved lemma')
        eq=tuple(map(freeze,entry['equation']))
        if len(eq)!=2 or sort(eq[0])!=sort(eq[1]) or sort(eq[0])!='L': raise Rejected('Not a list equation')
        cert=entry['certificate']; mode=cert['mode']; vs=params(eq)
        lean_name=('lib_' if library else 'held_')+nm
        if any(d['lean_name']==lean_name for d in self.audit['declarations']): raise Rejected('Duplicate declaration')
        start=len(self.lines)+1
        self.emit(); self.emit(f'-- Source {"library" if library else "held-out"} entry: {nm}')
        self.emit(f'theorem {lean_name}{binders(vs)} : {render(eq[0])} = {render(eq[1])} := by')
        if mode=='rewrite':
            self.branch(*eq,cert,self.rules,'  ',nm,'rewrite')
        elif mode=='induction':
            x=('v',name(cert['variable'])); tail=('v',name(cert['tail'])); head=('e',name(cert['head']))
            if x not in vs or tail in vs or head in vs or tail==x: raise Rejected('Induction variable/freshness invalid')
            generalized=[v for v in vs if v!=x]
            gen=' generalizing '+' '.join(map(varname,generalized)) if generalized else ''
            self.emit(f'  induction {varname(x)}{gen} with')
            self.emit('  | nil =>')
            self.branch(*(subst(t,{x:('nil',)}) for t in eq),cert['base'],self.rules,'    ',nm,'base')
            self.emit(f'  | cons {varname(head)} {varname(tail)} ih =>')
            ih_eq=tuple(subst(t,{x:tail}) for t in eq)
            rules=dict(self.rules)
            rules['IH']={'equation':ih_eq,'lean_name':'ih','params':generalized,'fixed':{tail}}
            self.branch(*(subst(t,{x:('cons',head,tail)}) for t in eq),cert['step'],rules,'    ',nm,'step')
        else: raise Rejected('Unknown proof mode')
        self.audit['declarations'].append({'name':nm,'lean_name':lean_name,'kind':'library' if library else 'held-out','mode':mode,'equation':eq,'start_line':start,'end_line':len(self.lines)})
        if library:
            self.rules[nm]={'equation':eq,'lean_name':lean_name,'params':vs,'fixed':set()}
            self.used_names.add(nm)
    def run(self):
        for entry in self.bundle['library']: self.entry(entry,True)
        for entry in self.bundle['proofs']: self.entry(entry,False)
        self.emit(); self.emit('-- Kernel axiom audit: these should all report no axioms.')
        for d in self.audit['declarations']: self.emit(f'#print axioms {d["lean_name"]}')
        self.emit('end CertificateReplay')
        self.audit['counts']={'library':len(self.bundle['library']),'held_out':len(self.bundle['proofs']),'recorded_rewrite_steps':len(self.audit['steps'])}
        return '\n'.join(self.lines)+'\n',self.audit

def translate_bytes(raw):
    return Exporter(json.loads(raw),hashlib.sha256(raw).hexdigest()).run()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('bundle',type=Path); parser.add_argument('output',type=Path)
    args=parser.parse_args()
    text,audit=translate_bytes(args.bundle.read_bytes())
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(text)
    args.output.with_suffix('.trace.json').write_text(json.dumps(audit,indent=2)+'\n')
    print(json.dumps(audit['counts'],sort_keys=True))
if __name__=='__main__': main()
