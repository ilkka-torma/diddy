def vadd(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] + b[i])
    return tuple(c)

def vsub(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] - b[i])
    return tuple(c)

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
