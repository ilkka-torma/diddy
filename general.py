def vsub(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] - b[i])
    return tuple(c)

def vadd(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] + b[i])
    return tuple(c)
