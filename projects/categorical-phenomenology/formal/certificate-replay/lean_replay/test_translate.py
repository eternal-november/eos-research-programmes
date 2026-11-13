"""Translation boundaries, generic terms, freshness, and trace preservation."""
import copy
import json
import unittest
from pathlib import Path
import translate as tr

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'experiment/results/guided_10000000_proofs.json'
X=('v','X'); N=('nil',); A=lambda x,y:('app',x,y)

class TranslationTests(unittest.TestCase):
    def setUp(self): self.bundle=json.loads(SOURCE.read_text())
    def reject(self,b):
        with self.assertRaises((tr.Rejected,KeyError,TypeError,IndexError)):
            tr.translate_bytes(json.dumps(b).encode())
    def test_complete_guided_counts(self):
        _,audit=tr.translate_bytes(SOURCE.read_bytes())
        self.assertEqual(audit['counts'],{'library':5,'held_out':15,'recorded_rewrite_steps':88})
    def test_trace_identical_to_certificate(self):
        _,audit=tr.translate_bytes(SOURCE.read_bytes())
        expected=[]
        for e in self.bundle['library']+self.bundle['proofs']:
            c=e['certificate']
            branches=[('rewrite',c)] if c['mode']=='rewrite' else [('base',c['base']),('step',c['step'])]
            for branch,c in branches:
                for side in ('left','right'):
                    for i,s in enumerate(c[side]):
                        expected.append((e['name'],branch,side,i,s['rule'],s.get('direction',1),s['path']))
        actual=[tuple(s[k] for k in ('entry','branch','side','index','rule','direction','path')) for s in audit['steps']]
        self.assertEqual(expected,actual)
    def test_wrong_path_rejected(self):
        self.bundle['library'][3]['certificate']['step']['left'][1]['path']=[2]
        self.reject(self.bundle)
    def test_wrong_rule_rejected(self):
        self.bundle['library'][3]['certificate']['step']['left'][4]['rule']='lemma_000'
        self.reject(self.bundle)
    def test_bad_direction_rejected(self):
        self.bundle['library'][3]['certificate']['step']['left'][4]['direction']=0
        self.reject(self.bundle)
    def test_omitted_critical_step_rejected(self):
        del self.bundle['library'][3]['certificate']['step']['left'][4]
        self.reject(self.bundle)
    def test_fresh_tail_rejected(self):
        self.bundle['library'][3]['certificate']['tail']='Y'
        self.reject(self.bundle)
    def test_fresh_head_rejected(self):
        b={'library':[], 'proofs':[{'name':'bad','equation':(('cons',('e','a'),X),('cons',('e','a'),X)), 'certificate':{'mode':'induction','variable':'X','head':'a','tail':'_t','base':{'left':[],'right':[]},'step':{'left':[],'right':[]}}}]}
        self.reject(b)
    def test_rigid_tail_not_arbitrarily_instantiated(self):
        b={'library':[], 'proofs':[{'name':'false_all_lists_nil','equation':(X,N),'certificate':{'mode':'induction','variable':'X','tail':'_t','head':'_a','base':{'left':[],'right':[]},'step':{'left':[{'rule':'IH','path':[]}],'right':[]}}}]}
        self.reject(b)
    def test_forward_reference_rejected(self):
        self.bundle['library'][0]['certificate']['base']['left'][0]['rule']='lemma_003'
        self.reject(self.bundle)
    def test_circular_dependency_rejected(self):
        self.bundle['library'][0]['certificate']['base']['left'][0]['rule']='lemma_000'
        self.reject(self.bundle)
    def test_duplicate_library_rejected(self):
        self.bundle['library'].append(copy.deepcopy(self.bundle['library'][0]))
        self.reject(self.bundle)
    def test_valid_reverse_direction_explicit_symmetry(self):
        b={'library':[], 'proofs':[{'name':'bad','equation':(X,X),'certificate':{'mode':'rewrite','left':[{'rule':'app_nil','path':[],'direction':-1}], 'right':[{'rule':'app_nil','path':[],'direction':-1}]}}]}
        # This reversal binds Y, so it is valid and explicitly uses Eq.symm.
        text,_=tr.translate_bytes(json.dumps(b).encode())
        self.assertIn('Eq.symm (app_nil',text)
    def test_ill_typed_equation_rejected(self):
        self.bundle['library'][0]['equation'][0][1]=['e','a']
        self.reject(self.bundle)
    def test_unused_learned_proofs_not_available(self):
        self.bundle['proofs'].append({'name':'invalid_reuse','equation':(X,X),'certificate':{'mode':'rewrite','left':[{'rule':'rev_nested','path':[]}],'right':[]}})
        self.reject(self.bundle)
    def test_bad_identifier_rejected(self):
        self.bundle['library'][0]['name']='oops\naxiom bad : False'
        self.reject(self.bundle)
    def test_generic_type_and_structural_induction(self):
        text,_=tr.translate_bytes(SOURCE.read_bytes())
        self.assertIn('variable {α : Type u}',text)
        self.assertIn('induction v_X generalizing v_Y with',text)
        self.assertIn('(ih (v_Y := (List.cons e__a v_Y)))',text)
        self.assertNotIn('simp ',text)
        self.assertNotIn('rw ',text)
        self.assertNotIn('sorry',text)

if __name__=='__main__': unittest.main(verbosity=2)
