#!/usr/bin/env python3
"""Finite A–F checks on actual graph/controller tables, with mutation regressions.
Not a proof of the all-generated theorem. Standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from itertools import product
from collections import Counter
from pathlib import Path
import hashlib, json

@dataclass(frozen=True)
class Event:
    key: object
    src: object
    tgt: object
    request: object
    reply: object

@dataclass
class Component:
    name: str
    states: tuple
    memories: tuple
    events: tuple[Event, ...]
    observation: dict
    action: dict
    update: dict
    initial: set
    support: set
    safe: set
    world: dict
    owner: str
    physical_id: str
    table_choice: str
    reads: frozenset = frozenset({'memory', 'observation', 'request', 'reply'})
    permitted_reads: frozenset = frozenset({'memory', 'observation', 'request', 'reply'})
    selector_program: object = None
    update_program: object = None

    def command(self, x, m):
        return self.action.get((m, self.observation[x]))

    def selected(self, e, m):
        return self.command(e.src, m) == e.request

    def commit(self, e, m):
        return self.update[(m, self.observation[e.src], e.request, e.reply)]

    def selected_records(self):
        return {(e.key, m) for x, m in self.support for e in self.events
                if e.src == x and self.selected(e, m)}

    def event_dict(self):
        return {e.key: e for e in self.events}

@dataclass
class Generator:
    name: str
    root: Component
    children: tuple[Component, ...]
    state_map: dict
    event_map: dict
    memory_map: dict
    joint_states: set
    joint_events: set
    exact: bool = True
    # Nullary semantics is a supplied retained boundary, NOT a singleton.
    boundary: Component | None = None
    assembly: object = None
    # Physical store occurrences, separate from repeated abstract component colors.
    occurrence_owners: tuple = ()
    def targets(self):
        return self.children if self.children else (self.boundary,)


@dataclass(frozen=True)
class Node:
    name: str
    physical_id: str
    inputs: tuple[str, ...]

@dataclass
class Program:
    ports: frozenset
    nodes: tuple[Node, ...]
    output: str
    tables: dict

    def evaluate(self, inputs):
        if not self.ports <= inputs.keys():
            raise ValueError('missing physical input port')
        values={k:inputs[k] for k in self.ports}
        for node in self.nodes:
            if node.name in values or any(k not in values for k in node.inputs):
                raise ValueError('unavailable read, duplicate producer, or forward/cyclic dependency')
            if node.physical_id not in self.tables:
                raise ValueError('undeclared physical primitive')
            key=tuple(values[k] for k in node.inputs)
            if key not in self.tables[node.physical_id]:
                raise ValueError('physical primitive not defined on actual ports')
            values[node.name]=self.tables[node.physical_id][key]
        if self.output not in values:
            raise ValueError('missing physical output')
        return values[self.output]


def request_program(n):
    ports=tuple('local'+str(i) for i in range(n))
    # Explicit finite primitive: synchronized equal requests, not inverse events.
    table={tuple(a for _ in ports):a for a in ('go','other')}
    return Program(frozenset(ports),(Node('request','synchronize'+str(n),ports),),
                   'request',{'synchronize'+str(n):table})


def compose_program(outer, inners):
    """Wire existing finite programs; do not invent a new wide primitive."""
    nodes=[]; tables={}; parent_outputs={}; count=0; ports=[]
    def merge(program):
        for pid,table in program.tables.items():
            if pid in tables and tables[pid]!=table:
                raise ValueError('different tables for same physical primitive')
            tables[pid]=table
    for i,inner in enumerate(inners):
        merge(inner)
        ordered=sorted(inner.ports,key=lambda s:int(s[5:]))
        names={old:'local'+str(count+j) for j,old in enumerate(ordered)}
        ports.extend(names.values());count+=len(ordered)
        for node in inner.nodes:
            name='inner'+str(i)+':'+node.name
            nodes.append(Node(name,node.physical_id,tuple(names[x] for x in node.inputs)))
            names[node.name]=name
        parent_outputs['local'+str(i)]=names[inner.output]
    merge(outer)
    names=dict(parent_outputs)
    for node in outer.nodes:
        name='outer:'+node.name
        nodes.append(Node(name,node.physical_id,tuple(names[x] for x in node.inputs)))
        names[node.name]=name
    return Program(frozenset(ports),tuple(nodes),names[outer.output],tables)


def check_program_registry(programs):
    tables={};failures=[]
    for program in programs:
        if program is None: continue
        for pid,table in program.tables.items():
            if pid in tables and tables[pid]!=table:
                failures.append(('E_shared_primitive_table',pid,'inconsistent physical program tables'))
            tables[pid]=table
    return failures


def check_component(c):
    failures = []
    fail = lambda clause, detail: failures.append((clause, c.name, repr(detail)))
    for kind,program,table in [('select',c.selector_program,c.action),('update',c.update_program,c.update)]:
        if program is None: continue  # Explicit raw-table fixtures remain distinguishable.
        for key,value in table.items():
            fields=('memory','observation') if kind=='select' else ('memory','observation','request','reply')
            inputs=dict(zip(fields,key))
            try:
                if not program.ports <= c.permitted_reads or program.evaluate(inputs)!=value:
                    fail('physical_compilation', (kind,key,value))
            except ValueError as err: fail('physical_compilation', (kind,str(err)))
    if not c.reads <= c.permitted_reads:
        fail('physical_read', c.reads-c.permitted_reads)
    if not c.initial <= c.support:
        fail('A_initial', c.initial-c.support)
    if not c.support <= c.safe:
        fail('A_safe', c.support-c.safe)
    if not c.support <= set(product(c.states, c.memories)):
        fail('support_type', c.support)
    events = c.event_dict()
    if len(events) != len(c.events):
        fail('record_identity', 'duplicate event key')
    for e in c.events:
        if e.src not in c.states or e.tgt not in c.states:
            fail('graph_incidence', e)
            continue
        if c.world[e.src] != c.world[e.tgt]:
            fail('persistent_world', e)
    for x, m in c.support:
        admitted = [e for e in c.events if e.src == x and c.selected(e, m)]
        if not admitted:
            fail('A_nonblocking', (x, m))
        for e in admitted:
            try:
                mt = c.commit(e, m)
            except KeyError:
                fail('physical_update_domain', (e.key, m))
                continue
            if (e.tgt, mt) not in c.support:
                fail('A_adverse_closure', (e.key, m, e.tgt, mt))
    # Exact least reachability is computed, not inferred from supplied support.
    reach = set(c.initial)
    while True:
        old = set(reach)
        for x, m in old:
            for e in c.events:
                if e.src == x and c.selected(e, m):
                    try: reach.add((e.tgt, c.commit(e, m)))
                    except KeyError: pass
        if reach == old: break
    if not reach <= c.support:
        fail('A_reachable_omission', reach-c.support)
    return failures, reach


def check_architecture(components, capacities):
    failures=check_program_registry([p for c in components for p in (c.selector_program,c.update_program)])
    chosen, owners = {}, {}
    for c in components:
        # Same physical identifier means the same actual tables, not just name.
        signature = (c.table_choice, repr(sorted(c.action.items(),key=repr)),
                     repr(sorted(c.update.items(),key=repr)))
        if c.physical_id in chosen and chosen[c.physical_id] != signature:
            failures.append(('E_shared_table', c.physical_id, 'different tables'))
        chosen[c.physical_id] = signature
        n = len(c.memories)
        if c.owner in owners and owners[c.owner] != n:
            failures.append(('physical_alias', c.owner, 'inconsistent store views'))
        owners[c.owner] = n
        if c.owner not in capacities or n > capacities[c.owner]:
            failures.append(('resource_bound', c.owner, n))
    return failures


def check_generator(g):
    failures = []
    fail = lambda clause, detail: failures.append((clause, g.name, repr(detail)))
    ts = g.targets()
    if not ts or any(t is None for t in ts):
        return [('nullary_boundary', g.name, 'missing retained boundary')]
    n = len(ts)
    evs = [c.event_dict() for c in ts]
    state_images, event_images = [], []
    owners=g.occurrence_owners or tuple(c.owner for c in ts)
    if len(owners)!=n: fail('B_owner_arity',owners)
    for row in g.joint_states:
        if len(row)!=n or any(pair not in c.support for c,pair in zip(ts,row)):
            fail('B_target_support_type',row)
        seen={}
        for owner,(_,memory) in zip(owners,row):
            if owner in seen and seen[owner]!=memory:
                fail('B_shared_store_alias', (owner,seen[owner],memory))
            seen[owner]=memory
    for x, m in g.root.support:
        if x not in g.state_map or m not in g.memory_map:
            fail('B_map_domain', (x,m)); continue
        xs, ms = g.state_map[x], g.memory_map[m]
        if len(xs)!=n or len(ms)!=n:
            fail('B_arity', (xs,ms)); continue
        if g.assembly is None:
            fail('C_physical_assembly', 'missing actual request assembly')
        else:
            try:
                local_commands={'local'+str(i):c.command(xi,mi) for i,(c,xi,mi) in enumerate(zip(ts,xs,ms))}
                if g.assembly.evaluate(local_commands)!=g.root.command(x,m):
                    fail('C_physical_assembly', (x,m,local_commands,g.root.command(x,m)))
            except ValueError as err: fail('C_physical_assembly', str(err))
        joint = tuple(zip(xs,ms))
        state_images.append(joint)
        if joint not in g.joint_states:
            fail('B_joint_state', joint)
        for c, pair in zip(ts,joint):
            if pair not in c.support: fail('B_local_support', pair)
        for e in g.root.events:
            if e.src != x: continue
            if e.key not in g.event_map:
                fail('graph_event_domain', e.key); continue
            keys = g.event_map[e.key]
            if len(keys)!=n or any(k not in d for k,d in zip(keys,evs)):
                fail('graph_event_type', keys); continue
            es = [d[k] for k,d in zip(keys,evs)]
            if tuple(a.src for a in es)!=xs or tuple(a.tgt for a in es)!=g.state_map[e.tgt]:
                fail('graph_incidence', e.key)
            root_selected=g.root.selected(e,m)
            local_selected=all(c.selected(a,mi) for c,a,mi in zip(ts,es,ms))
            if root_selected and not local_selected:
                fail('C_command', (e.key,m,root_selected,local_selected))
            if not root_selected: continue
            image=tuple((a.key,mi) for a,mi in zip(es,ms))
            event_images.append(image)
            if image not in g.joint_events: fail('C_joint_event', image)
            try:
                lhs=g.memory_map[g.root.commit(e,m)]
                rhs=tuple(c.commit(a,mi) for c,a,mi in zip(ts,es,ms))
                if lhs!=rhs: fail('D_update_cube', (e.key,m,lhs,rhs))
            except KeyError as err:
                fail('D_update_domain', str(err))
    if g.exact:
        if Counter(state_images)!=Counter({x:1 for x in g.joint_states}):
            fail('F_state_bijection', {'images':len(state_images),'target':len(g.joint_states)})
        if Counter(event_images)!=Counter({x:1 for x in g.joint_events}):
            fail('F_event_bijection', {'images':len(event_images),'target':len(g.joint_events)})
    # Target relation must be an actual coupled subgraph.
    joint_state_set=set(g.joint_states)
    for row in g.joint_events:
        try:
            if any(not c.selected(d[k],m) for c,d,(k,m) in zip(ts,evs,row)):
                fail('F_target_unselected_record',row)
            src=tuple((d[k].src,m) for d,(k,m) in zip(evs,row))
            tgt=tuple((d[k].tgt,c.commit(d[k],m)) for c,d,(k,m) in zip(ts,evs,row))
            if len(row)!=n or src not in joint_state_set or tgt not in joint_state_set:
                fail('F_target_subgraph', row)
        except KeyError:
            fail('F_target_record', row)
    return failures


def check_presentation(components, generators, equations, capacities):
    failures=check_architecture(components,capacities)
    failures+=check_program_registry([p for c in components for p in (c.selector_program,c.update_program)]
                                    +[g.assembly for g in generators])
    for c in components: failures+=check_component(c)[0]
    for g in generators: failures+=check_generator(g)
    for equation in equations: failures+=check_equation(*equation)
    return failures


def check_equation(g, h, owner_transport=None):
    failures=[]
    go=g.occurrence_owners or tuple(c.owner for c in g.targets())
    ho=h.occurrence_owners or tuple(c.owner for c in h.targets())
    if owner_transport is None:
        owner_transport={x:x for x in go}
    if (set(owner_transport)!=set(go) or set(owner_transport.values())!=set(ho)
        or len(set(owner_transport.values()))!=len(owner_transport)
        or tuple(owner_transport.get(x) for x in go)!=ho):
        failures.append(('E_physical_owner_transport',g.name,h.name))
    if g.root is not h.root or g.targets()!=h.targets():
        return [('E_parallel_type',g.name,h.name)]
    for x,m in g.root.support:
        if g.state_map[x]!=h.state_map[x] or g.memory_map[m]!=h.memory_map[m]:
            failures.append(('E_state_memory_equation',g.name,repr((x,m))))
    for e,m in g.root.selected_records():
        if g.event_map[e]!=h.event_map[e]:
            failures.append(('E_event_equation',g.name,repr((e,m))))
    if g.joint_states!=h.joint_states or g.joint_events!=h.joint_events:
        failures.append(('E_joint_target_equation',g.name,h.name))
    return failures


def product_component(n, name, correlated=False, hidden_reply=False, world_persistent=False):
    states=tuple(product((0,1),repeat=n))
    if correlated: states=tuple(x for x in states if len(set(x))<=1)
    memories=states
    masks=states
    events=tuple(Event((x,v),x,tuple(a^b for a,b in zip(x,v)),'go',0 if hidden_reply else v)
                 for x in states for v in masks)
    obs={x:0 for x in states}
    action={(m,0):'go' for m in memories}
    update={(m,0,'go',0 if hidden_reply else v):m if hidden_reply else tuple(a^b for a,b in zip(m,v))
            for m in memories for v in masks}
    support={(x,x) for x in states}
    return Component(name,states,memories,events,obs,action,update,set(support),set(support),
                     set(product(states,memories)),
                     {x:x[0] if world_persistent else 0 for x in states},name,name,'xor',
                     selector_program=Program(frozenset(),(Node('a','select',()),),'a',{'select':{():'go'}}),
                     update_program=Program(frozenset({'memory','reply'}),(Node('m','commit:'+name,('memory','reply')),),'m',
                        {'commit:'+name:{(m,0 if hidden_reply else v):m if hidden_reply else tuple(a^b for a,b in zip(m,v))
                                   for m in memories for v in masks}}))


def split(root, children, lengths, name='split'):
    offsets=[sum(lengths[:i]) for i in range(len(lengths))]
    cut=lambda x:tuple(tuple(x[j:j+n]) for j,n in zip(offsets,lengths))
    sm={x:cut(x) for x in root.states}
    mm={m:cut(m) for m in root.memories}
    em={e.key:tuple((x,v) for x,v in zip(cut(e.src),cut(e.key[1]))) for e in root.events}
    js={tuple(zip(sm[x],mm[m])) for x,m in root.support}
    je={tuple(zip(em[k],mm[m])) for k,m in root.selected_records()}
    return Generator(name,root,tuple(children),sm,em,mm,js,je,assembly=request_program(len(children)),
                     occurrence_owners=tuple(root.owner+':occ'+str(i) for i in range(len(children))))


def substitute(g, refinements, name='composite'):
    """Relational substitution of actual JOINT supports, not independent join."""
    assert g.children and len(g.children)==len(refinements)
    assert all(h.root is c and h.children for c,h in zip(g.children,refinements))
    targets=tuple(c for h in refinements for c in h.children)
    def flatten_maps(row, key):
        return tuple(v for x,h in zip(row,refinements) for v in getattr(h,key)[x])
    sm={x:flatten_maps(row,'state_map') for x,row in g.state_map.items()}
    em={e:flatten_maps(row,'event_map') for e,row in g.event_map.items()}
    mm={m:flatten_maps(row,'memory_map') for m,row in g.memory_map.items()}
    def relation_image(rows, event=False):
        out=set()
        for row in rows:
            flat=[]
            for (x,m),h in zip(row,refinements):
                xs=(h.event_map if event else h.state_map)[x]
                image=tuple(zip(xs,h.memory_map[m]))
                assert image in (h.joint_events if event else h.joint_states)
                flat.extend(image)
            out.add(tuple(flat))
        return out
    return Generator(name,g.root,targets,sm,em,mm,relation_image(g.joint_states),
                     relation_image(g.joint_events,True),g.exact and all(h.exact for h in refinements),
                     assembly=compose_program(g.assembly,[h.assembly for h in refinements]),
                     occurrence_owners=tuple((g.occurrence_owners or tuple(c.owner for c in g.targets()))[i]+'/'+owner
                        for i,h in enumerate(refinements)
                        for owner in (h.occurrence_owners or tuple(c.owner for c in h.targets()))))


def identity(c):
    return split(c,[c],[len(c.states[0])], 'identity')


def factor_table(rows, input_columns, output_column):
    table={}
    for row in rows:
        key=tuple(row[i] for i in input_columns); out=row[output_column]
        if key in table and table[key]!=out:
            return None, {'input':key,'outputs':(table[key],out)}
        table[key]=out
    return table,None


def common_action_table(rows, input_columns, demand_column):
    fibres={}
    for row in rows:
        key=tuple(row[i] for i in input_columns)
        demand=set(row[demand_column])
        fibres[key]=demand if key not in fibres else fibres[key] & demand
    return fibres, {key for key, demand in fibres.items() if not demand}


def run():
    results=[]
    def expect(name, failures, should_pass, required=None):
        passed=not failures
        assert passed==should_pass,(name,failures)
        if required: assert any(f[0]==required for f in failures),(name,required,failures)
        results.append({'name':name,'expected':'PASS' if should_pass else 'REJECT',
                        'observed':'PASS' if passed else 'REJECT',
                        'failure_clauses':sorted({f[0] for f in failures})})
    leaf=product_component(1,'leaf')
    pair=product_component(2,'pair')
    root=product_component(3,'root')
    for c in [leaf,pair,root]:
        expect('component_'+c.name,check_component(c)[0],True)
    g=split(root,[pair,leaf],[2,1],'first_pair')
    h=split(pair,[leaf,leaf],[1,1],'pair_leaves')
    k=split(root,[leaf,pair],[1,2],'last_pair')
    for a in [g,h,k]: expect('primitive_'+a.name,check_generator(a),True)
    left=substitute(g,[h,identity(leaf)],'left_flattening')
    right=substitute(k,[identity(leaf),h],'right_flattening')
    expect('left_nested',check_generator(left),True)
    expect('right_nested',check_generator(right),True)
    assert (left.state_map,left.event_map,left.memory_map,left.joint_states,left.joint_events)==(right.state_map,right.event_map,right.memory_map,right.joint_states,right.joint_events)
    transport=dict(zip(left.occurrence_owners,right.occurrence_owners))
    expect('crossing_both_orders_actual_maps',check_equation(left,right,transport),True)
    expect('crossing_requires_named_store_transport',check_equation(left,right),False,'E_physical_owner_transport')
    # General depth stress, occurrence addresses retained by tuple position.
    trees=0
    def trees_on(n):
        c=product_component(n,'n'+str(n))
        if n==1: return [(c,identity(c))]
        out=[]
        for cut in range(1,n):
            for lc,lg in trees_on(cut):
                for rc,rg in trees_on(n-cut):
                    outer=split(c,[lc,rc],[cut,n-cut])
                    comp=substitute(outer,[lg,rg])
                    assert not check_generator(comp)
                    out.append((c,comp))
        return out
    for n in range(1,5):
        ts=trees_on(n); trees+=len(ts)
        canonical=ts[0][1]
        for c,t in ts:
            assert (t.state_map,t.event_map,t.memory_map)==(canonical.state_map,canonical.event_map,canonical.memory_map)
    results.append({'name':'generated_binary_trees_through_four_leaves','expected':'PASS','observed':'PASS','trees':trees})
    # D mutation: still a permitted table and total support, but cube breaks.
    bad=product_component(1,'bad_update')
    bad.update={key:key[0] for key in bad.update}
    bad.support=set(product(bad.states,bad.memories))
    mut=split(pair,[bad,leaf],[1,1],'bad_cube')
    expect('update_cube_mutation',check_generator(mut),False,'D_update_cube')
    cmd=product_component(1,'bad_command');cmd.action={key:'other' for key in cmd.action}
    expect('command_mutation',check_generator(split(pair,[cmd,leaf],[1,1])),False,'C_command')
    bad_assembly=replace(h,assembly=Program(frozenset({'local0','local1'}),
                      (Node('req','cheat',('hidden_reply',)),),'req',{'cheat':{(0,):'go'}}))
    expect('request_assembly_forbidden_future_reply',check_generator(bad_assembly),False,'C_physical_assembly')
    independent_alpha=replace(leaf,action={key:'other' for key in leaf.action})
    expect('independent_alpha_not_physical_compilation',check_component(independent_alpha)[0],False,'physical_compilation')
    cyclic=Program(frozenset(),(Node('a','id',('b',)),Node('b','id',('a',))),'a',{'id':{('go',):'go'}})
    try: cyclic.evaluate({}); raise AssertionError('cycle accepted')
    except ValueError: pass
    results.append({'name':'phase_DAG_cycle_rejected','expected':'REJECT','observed':'REJECT'})
    badmap=replace(h,state_map=dict(h.state_map))
    badmap.state_map[(0,1)]=((0,),(0,))
    expect('state_representation_mutation',check_generator(badmap),False,'graph_incidence')
    shared=replace(leaf,name='same_physical_different_table',table_choice='identity')
    expect('repeated_physical_table',check_architecture([leaf,shared],{'leaf':2}),False,'E_shared_table')
    expect('same_physical_shared_table',check_architecture([leaf,leaf],{'leaf':2}),True)
    expect('compiled_root_local_program_registry',check_architecture([leaf,pair,root],{'leaf':2,'pair':4,'root':8}),True)
    p1=Program(frozenset(),(Node('a','same_physical',()),),'a',{'same_physical':{():'go'}})
    p2=Program(frozenset(),(Node('a','same_physical',()),),'a',{'same_physical':{():'other'}})
    expect('same_primitive_in_two_programs',check_program_registry([p1,p2]),False,'E_shared_primitive_table')
    hidden_choice=replace(leaf,update={key:key[0] for key in leaf.update})
    expect('same_label_different_actual_table',check_architecture([leaf,hidden_choice],{'leaf':2}),False,'E_shared_table')
    expect('actual_memory_budget',check_architecture([pair],{'pair':2}),False,'resource_bound')
    extra=product_component(1,'undeclared_selector')
    expect('no_extra_selector',check_architecture([leaf,extra],{'leaf':2}),False,'resource_bound')
    forbidden=replace(leaf,reads=leaf.reads|{'hidden_event_bit'})
    expect('forbidden_hidden_read',check_component(forbidden)[0],False,'physical_read')
    rows=[(m,0,v,m[0]^v[0]) for m in leaf.memories for v in leaf.states]
    _,conflict=factor_table(rows,[0,1],3)
    assert conflict is not None
    table,conflict2=factor_table(rows,[0,1,2],3)
    assert conflict2 is None and len(table)==4
    results.append({'name':'same_actual_records_hidden_vs_delivered_reply','expected':'REJECT/PASS','observed':'REJECT/PASS','hidden_conflict':conflict})
    demands=[(0,0,{'a','b'}),(1,0,{'b','c'}),(2,0,{'a','c'})]
    assert all(demands[i][2]&demands[j][2] for i in range(3) for j in range(i))
    _,empty=common_action_table(demands,[1],2)
    assert empty=={(0,)}
    _,separate_empty=common_action_table(demands,[0,1],2)
    assert not separate_empty
    results.append({'name':'terminal_all_world_intersection_not_pairwise','expected':'REJECT/PASS','observed':'REJECT/PASS'})
    persistent=product_component(1,'resampled_world',world_persistent=True)
    expect('persistent_theta_mutation',check_component(persistent)[0],False,'persistent_world')
    # Correlated root: exact only onto witnessed JOINT support, not full Dyn tuple.
    corr=product_component(2,'correlated',correlated=True)
    cg=split(corr,[leaf,leaf],[1,1],'correlated_split')
    expect('joint_relative_exactness',check_generator(cg),True)
    shared_store=replace(cg,occurrence_owners=('actual_shared','actual_shared'))
    expect('shared_store_diagonal_valid',check_generator(shared_store),True)
    inconsistent_store=replace(h,occurrence_owners=('actual_shared','actual_shared'))
    expect('repeated_color_is_not_shared_store',check_generator(inconsistent_store),False,'B_shared_store_alias')
    joined_states=set(product(leaf.support,repeat=2))
    joined_events=set(product(leaf.selected_records(),repeat=2))
    full=replace(cg,joint_states=joined_states,joint_events=joined_events)
    expect('relative_exact_is_not_full_dynamic_exact',check_generator(full),False,'F_state_bijection')
    arbitrary=replace(left,joint_states=left.joint_states|{(((0,),(1,)),((0,),(0,)),((0,),(0,)))})
    expect('arbitrary_higher_joint_target',check_generator(arbitrary),False,'F_state_bijection')
    expect('equation_must_compare_joint_target',check_equation(left,arbitrary),False,'E_joint_target_equation')
    # Relative exactness does not require reverse command implication outside J.
    s0=(0,)
    r=product_component(1,'restricted_root')
    r.states=r.memories=(s0,);r.observation={s0:0};r.world={s0:0}
    r.initial=r.support=r.safe={(s0,s0)}
    r.action={(s0,0):'go'};r.update={(s0,0,'go',0):s0}
    r.events=(Event('chosen',s0,s0,'go',0),Event('outside',s0,s0,'other',0))
    l=replace(r,name='ambient_local',owner='ambient_local',physical_id='ambient_local',
              events=(Event('chosen',s0,s0,'go',0),Event('outside',s0,s0,'go',0)))
    relative=Generator('relative_command',r,(l,),{s0:(s0,)},
                       {'chosen':('chosen',),'outside':('outside',)}, {s0:(s0,)},
                       {((s0,s0),)},{(('chosen',s0),)},assembly=request_program(1))
    expect('ambient_reverse_command_not_required',check_generator(relative),True)
    full_target=replace(relative,joint_events={(('chosen',s0),),(('outside',s0),)})
    expect('retained_joint_reverse_coverage_required',check_generator(full_target),False,'F_event_bijection')
    unselected_local=replace(l,events=(Event('chosen',s0,s0,'go',0),Event('outside',s0,s0,'other',0)),
                             update={(s0,0,'go',0):s0,(s0,0,'other',0):s0})
    invalid_target=replace(full_target,children=(unselected_local,),exact=False)
    expect('nonexact_target_still_selected_subgraph',check_generator(invalid_target),False,'F_target_unselected_record')
    # Nullary boundary is an actual two-state/two-memory graph.
    boundary=product_component(1,'boundary')
    null=Generator('nullary',leaf,(),{x:(x,) for x in leaf.states},
        {e.key:(e.key,) for e in leaf.events},{m:(m,) for m in leaf.memories},
        {((x,m),) for x,m in leaf.support},{((e,m),) for e,m in leaf.selected_records()},True,boundary,request_program(1))
    expect('nullary_retained_memory_boundary',check_generator(null),True)
    collapse=replace(null,memory_map={m:((0,),) for m in leaf.memories})
    expect('nullary_point_collapse',check_generator(collapse),False,'D_update_cube')
    missing=replace(null,boundary=None)
    expect('nullary_no_boundary',check_generator(missing),False,'nullary_boundary')
    # Omit a reachable adverse successor from initial support: actual closure detects.
    omitted=product_component(1,'omitted');omitted.initial={((0,),(0,))};omitted.support=set(omitted.initial)
    expect('all_adverse_support_closure',check_component(omitted)[0],False,'A_adverse_closure')
    expect('aggregate_all_physical_programs',check_presentation([leaf,pair,root],[g,h,k,left,right],[(left,right,transport)],
        {'leaf':2,'pair':4,'root':8}),True)
    conflicting_assembly=replace(h.assembly,tables={'synchronize2':{('go','go'):'other',('other','other'):'other'}})
    conflicting_g=replace(h,assembly=conflicting_assembly)
    expect('assembly_registry_cannot_override_same_primitive',
        check_presentation([leaf,pair,root],[g,h,conflicting_g],[],{'leaf':2,'pair':4,'root':8}),
        False,'E_shared_primitive_table')
    return {'status':'PASS','scope':'Finite table checker/regressions, not theorem proof or Lean verification',
            'checks':results,'check_count':len(results),'all_expected_results':True}

if __name__=='__main__':
    result=run()
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['theory_sha256']=hashlib.sha256((Path(__file__).parent.parent/'theory/Typed_Causal_Presentation_Closure.md').read_bytes()).hexdigest()
    out=Path(__file__).with_name('check_typed_causal_presentation_results.json')
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))
