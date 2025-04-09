import math
def vadd(u, v):
    return tuple(a[0]+a[1] for a in zip(u, v))
def vsub(u, v):
    return tuple(a[0]-a[1] for a in zip(u, v))
def smul(s, u):
    return tuple(s*a for a in u)
def vmul(u, v):
    return tuple(a[0]*a[1] for a in zip(u, v))
def vdot(u, v):
    return sum(vmul(u, v))
def same_dimize(u, v):
    if len(u) < len(v):
        return u + tuple(0 for i in range(len(v) - len(u))), v
    else:
        return u, v + tuple(0 for i in range(len(u) - len(v)))
def distance(u, v):
    u, v = same_dimize(u, v)
    w = vsub(u, v)
    return math.sqrt(vdot(w, w))
def flipy(t):
    return flip_coord(t, 1)
def flip_coord(t, i):
    return t[:i] + (t[i],) + t[i+1:]
def zero_vector(dim):
    return tuple(0 for i in range(dim))
def char_vector(dim, j):
    return tuple(int(i==j) for i in range(dim))
def in_hyperrectangle(v, dims):
    for (d, (a, b)) in zip(v, dims):
        if not (a <= d <= b):
            return False
    return True
# general floodfill operation, start from something, and add
# neighbors by some rule while condition holds
def floodfill(start, cond, nbrs, reversible_optimize=False):
    if reversible_optimize:
        return floodfill_ro(start, cond, nbrs)
    seen = set([start])
    frontier = set([start])
    while frontier:
        #print(frontier)
        newfrontier = set()
        for f in frontier:
            for n in nbrs(f):
                if not cond(n):
                    continue
                if n in seen:
                    continue
                seen.add(n)
                newfrontier.add(n)
        frontier = newfrontier
    return seen
def floodfill_ro(start, cond, nbrs):
    ret = list()
    oldfrontier = set([])
    frontier = set([start])
    while frontier:
        newfrontier = set()
        for f in frontier:
            for n in nbrs(f):
                if not cond(n):
                    continue
                if n in oldfrontier or n in frontier or n in newfrontier:
                    continue
                newfrontier.add(n)
                ret.append(n)
        oldfrontier = frontier
        frontier = newfrontier
    return ret
def closest_vector(us, v):
    if len(us) == 0:
        return None
    minp = None
    mind = 1000000000000000000000000
    for p in us:
        d = distance(p, v)
        if d < mind:
            mind = d
            minp = p
    return minp
