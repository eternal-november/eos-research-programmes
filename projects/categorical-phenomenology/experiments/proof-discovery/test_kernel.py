"""Adversarial tests independent of the proof-search algorithm."""
import copy,json,unittest
from pathlib import Path
import kernel as k

N=('nil',);X=('v','X');T=('v','_t');a=('e','a');h=('e','_a')
C=lambda x,y:('cons',x,y)
A=lambda x,y:('app',x,y)
R=lambda x:('rev',x)

class KernelSafety(unittest.TestCase):
    def reject(self,eq,cert,library=None):
        with self.assertRaises((k.Rejected,KeyError,TypeError,IndexError)):
            k.check_equation(eq,cert,library or {})
    def test_reflexivity(self):
        k.check_equation((X,X),{'mode':'rewrite','left':[],'right':[]},{})
    def test_definitions(self):
        k.check_equation((A(N,X),X),{'mode':'rewrite','left':[{'rule':'app_nil','path':[]}],'right':[]},{})
    def test_false_reflexivity(self):
        self.reject((X,N),{'mode':'rewrite','left':[],'right':[]})
    def test_ill_typed_list(self):
        self.reject((A(a,X),X),{'mode':'rewrite','left':[],'right':[]})
    def test_ill_typed_head(self):
        self.reject((C(X,N),C(X,N)),{'mode':'rewrite','left':[],'right':[]})
    def test_unknown_lemma(self):
        self.reject((X,N),{'mode':'rewrite','left':[{'rule':'self','path':[]}],'right':[]})
    def test_fake_ih_cannot_instantiate_tail(self):
        # If the IH were an ordinary universally quantified rewrite, X=[]
        # would falsely prove every finite list empty at the cons case.
        cert={'mode':'induction','variable':'X','tail':'_t','head':'_a',
              'base':{'left':[],'right':[]},
              'step':{'left':[{'rule':'IH','path':[]}],'right':[]}}
        self.reject((X,N),cert)
    def test_legitimate_fixed_tail_ih(self):
        # Right identity by induction, including a fixed-tail IH under cons.
        cert={'mode':'induction','variable':'X','tail':'_t','head':'_a',
              'base':{'left':[{'rule':'app_nil','path':[]}],'right':[]},
              'step':{'left':[{'rule':'app_cons','path':[]},{'rule':'IH','path':[2]}],'right':[]}}
        k.check_equation((A(X,N),X),cert,{})
    def test_tail_freshness(self):
        cert={'mode':'induction','variable':'X','tail':'X','head':'_a','base':{'left':[],'right':[]},'step':{'left':[],'right':[]}}
        self.reject((X,X),cert)
    def test_head_freshness(self):
        cert={'mode':'induction','variable':'X','tail':'_t','head':'a','base':{'left':[],'right':[]},'step':{'left':[],'right':[]}}
        self.reject((C(a,X),C(a,X)),cert)
    def test_wrong_induction_sort(self):
        cert={'mode':'induction','variable':'a','tail':'_t','head':'_a','base':{'left':[],'right':[]},'step':{'left':[],'right':[]}}
        self.reject((C(a,N),C(a,N)),cert)
    def test_wrong_path(self):
        self.reject((A(N,X),X),{'mode':'rewrite','left':[{'rule':'app_nil','path':[0]}],'right':[]})
    def test_reverse_direction_cannot_invent_variables(self):
        self.reject((X,X),{'mode':'rewrite','left':[{'rule':'bad','path':[],'direction':-1}],'right':[]},{'bad':(A(X,('v','Y')),X)})
    def test_circular_bundle(self):
        bundle={'library':[{'name':'circular','equation':(X,N),'certificate':{'mode':'rewrite','left':[{'rule':'circular','path':[]}],'right':[]}}],'proofs':[]}
        with self.assertRaises(k.Rejected):k.check_bundle(bundle)
    def test_reserved_name_bundle(self):
        bundle={'library':[{'name':'IH','equation':(X,X),'certificate':{'mode':'rewrite','left':[],'right':[]}}],'proofs':[]}
        with self.assertRaises(k.Rejected):k.check_bundle(bundle)
    def test_saved_bundles(self):
        for path in (Path(__file__).parent/'results').glob('*_proofs.json'):
            k.check_bundle(json.loads(path.read_text()))

if __name__=='__main__':unittest.main(verbosity=2)
