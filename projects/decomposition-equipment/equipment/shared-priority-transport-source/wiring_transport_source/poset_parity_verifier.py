"""Independent verifier: no imports from producer, no extension enumeration.
Input follows poset_parity_checker.certify. CERTIFIED verification relies on the
proved adjacent-swap theorem; failure verification only checks explicit orders.
"""

def verify(n, edges, roles, bits, cert, required=None):
    if n < 0 or len(roles) != n or len(bits) != n or any(b not in (0,1) for b in bits):
        return False
    outgoing = [[] for _ in range(n)]
    for i,j in edges:
        if not 0 <= i < n or not 0 <= j < n:
            return False
        outgoing[i].append(j)
    # Independent DFS reachability rather than producer's Warshall closure.
    reach = []
    for start in range(n):
        visited = set()
        todo = outgoing[start][:]
        while todo:
            v = todo.pop()
            if v not in visited:
                visited.add(v)
                todo.extend(outgoing[v])
        if start in visited:
            return False
        reach.append(visited)
    def valid(order):
        if len(order)!=n or set(order)!=set(range(n)):
            return False
        position = dict(zip(order,range(n)))
        return all(position[i]<position[j] for i,j in edges)
    def value(order):
        return {r:sum(bits[k] for k,j in enumerate(order) if roles[j]==r)%2 for r in roles}
    status=cert.get('status')
    if status=='NONINVARIANT':
        orders=cert.get('orders',[])
        return len(orders)==2 and all(valid(o) for o in orders) and value(orders[0])!=value(orders[1])
    order=cert.get('order',[])
    if not valid(order):
        return False
    actual=value(order)
    if status=='TARGET_MISMATCH':
        return required is not None and actual != required
    if status!='CERTIFIED' or cert.get('parity')!=actual or (required is not None and actual!=required):
        return False
    for i in range(n):
        for j in range(i):
            if roles[i]==roles[j] or j in reach[i] or i in reach[j]:
                continue
            ancestors=sum(i in reach[v] or j in reach[v] for v in range(n))
            descendants=len(reach[i] | reach[j])
            # Boundaries t split t prefix jobs from n-t suffix jobs.
            for t in range(1,n):
                if ancestors < t < n-descendants and bits[t-1]!=bits[t]:
                    return False
    return True
