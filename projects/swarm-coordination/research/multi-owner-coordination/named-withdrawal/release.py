"""Fail closed on ambiguous or unrecognized ownership/identity evidence."""

def lawful(confirmed_right,possible,permitted):
    if not confirmed_right or not possible:
        return False
    return set(possible)<=set(permitted)

def role_signatures(n,withdrawals):
    return tuple(tuple(j in w for w in withdrawals) for j in range(n))

def placement_profile(placement,signatures):
    return tuple(signatures[j] for j in placement)
