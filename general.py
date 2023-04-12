def vadd(vec1, vec2):
    return tuple(a+b for (a,b) in zip(vec1, vec2))

def vsub(vec1, vec2):
    return tuple(a-b for (a,b) in zip(vec1, vec2))

def vmod(m, v):
    return v[0]%m, v[1]%m

def Z2square(rad):
    for x in range(-rad, rad+1):
        for y in range(-rad, rad+1):
            yield (x, y)

def centered_hypercube(dim, rad):
    if dim == 0:
        yield ()
        return
    for v in centered_hypercube(dim-1, rad):
        for a in range(-rad, rad+1):
            yield v + (a,)

def Z2onesidedsquare(rad):
    for x in range(0, rad):
        for y in range(0, rad):
            yield (x, y)

def onesided_hypercube(dim, rad):
    if dim == 0:
        yield ()
        return
    for v in centered_hypercube(dim-1, rad):
        for a in range(0, rad):
            yield v + (a,)
