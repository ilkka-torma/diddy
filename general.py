def vadd(vec1, vec2):
    return tuple(a+b for (a,b) in zip(vec1, vec2))

def vsub(vec1, vec2):
    return tuple(a-b for (a,b) in zip(vec1, vec2))

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

def vmod(m, vec):
    return tuple(a%m for a in vec)

def nvmod(m, nvec):
    return tuple(a%m for a in nvec[:-1]) + nvec[-1:]

def vneg(vec):
    return tuple(-a for a in vec)

def nvadd(nvec, vec):
    return tuple(a+b for (a,b) in zip(nvec, vec)) + nvec[-1:]

def nvsub(nvec, vec):
    return tuple(a-b for (a,b) in zip(nvec, vec)) + nvec[-1:]

def pats(domain, alph):
    if not domain:
        yield dict()
    else:
        vec = domain.pop()
        for pat in pats(domain, alph):
            for c in alph[:-1]:
                pat2 = pat.copy()
                pat2[vec] = c
                yield pat2
            pat[vec] = alph[-1]
            yield pat
        domain.add(vec)

