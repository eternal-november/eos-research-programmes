"""Replacement provider: independently coded fixed bank, no other module."""
def publish(n, r, read):
    idle = []
    for cell in range(r+1):
        if read(cell):
            idle.append(cell)
    assert idle
    return idle[0], 2

def published_late(n, r, read):
    lane,_=publish(n,r,read)
    return lane,3
