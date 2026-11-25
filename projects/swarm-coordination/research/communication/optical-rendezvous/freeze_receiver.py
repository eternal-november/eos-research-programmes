import contextlib,io,json,hashlib
with contextlib.redirect_stdout(io.StringIO()):
    import replay as r

def compiled_table():
    rows=r.solve(r.nom,7,True,witness=True)
    assert rows
    table={}
    histories=[()]*len(r.nom)
    states=[r.INIT]*len(r.nom)
    for t,row in rows:
        for i,(w,before,(_,act,after)) in enumerate(zip(r.nom,states,row)):
            key=histories[i]+(r.view(w,before,1),)
            assert table.setdefault(key,act)==act
            histories[i]=key+((act,),)
            states[i]=after
    return tuple(sorted(table.items()))

def canonical(x):
    return json.dumps(x,separators=(",",":"),sort_keys=True)+"\n"

if __name__=="__main__":
    data=canonical(compiled_table()).encode()
    assert open("receiver_policy.json","rb").read()==data
    print("frozen receiver",len(compiled_table()),"local decision entries",hashlib.sha256(data).hexdigest())
