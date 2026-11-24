"""Outgoing provider: reverse-order whole-grid scan, no controller imports."""
def publish(n, r, read):
    values=[(i,read(i)) for i in range(n-1,-1,-1)]
    return next(i for i,idle in values if idle), 2
