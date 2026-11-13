#!/usr/bin/env python3
"""Finite certificate for the independent Mixed Boolean relational assignment.
The uniform relation-calculus laws are P evidence in relational/RelationalTargetProof.md.
This eight-input check is not a proof for arbitrary signatures or presentations.
"""
import itertools, json
colors = {'a': (0,1), 'b': (1,2), 'c': (2,3), 'd': (0,2), 'e': (1,3), 'whole': (0,3)}
profiles = {'split12': (['a','b'],'d'), 'split23': (['b','c'],'e'),
            'cut12_3': (['d','c'],'whole'), 'cut1_23': (['a','e'],'whole'),
            'red': (['whole'],'whole'), 'blue': (['whole'],'whole')}
for inputs, output in profiles.values():
    assert colors[inputs[0]][0] == colors[output][0]
    assert colors[inputs[-1]][1] == colors[output][1]
    assert all(colors[a][1] == colors[b][0] for a,b in zip(inputs, inputs[1:]))
rows=[]
for x,y,z in itertools.product(range(2),repeat=3):
    left=(x^y)^z; right=x^(y^z)
    assert left==right
    rows.append({'input':[x,y,z],'left_output':left,'right_output':right})
separators=[{'input':x,'red_output':x,'blue_output':1-x} for x in range(2)]
assert all(x['red_output']!=x['blue_output'] for x in separators)
mutant_failures=[list(x) for x in itertools.product(range(2),repeat=3)
                 if ((x[0]^x[1])^x[2]) != (x[0]^(x[1]|x[2]))]
assert mutant_failures
print(json.dumps({'status':'PASS','interfaces':[0,1,2,3],'profiles':profiles,
                  'declaration_inputs_exhaustive':rows,'undeclared_separators':separators,
                  'or_mutation_detected_inputs':mutant_failures},indent=2))
