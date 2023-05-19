import frozendict
fd = frozendict.FrozenDict
INFINITE = "infinite"
LOOPS = "loops"

# given tfg element and substitution, calculate order
def calculate_order(tfg, sub):
    lrad, rrad = bound_rad(tfg)
    rad = lrad + rrad
    #print(rad)
    #print(lorder, rorder)
    images = iterate_sub_until_lengths(sub, rad * 3)
    #print(images)
    structures = {}
    loops = set()
    for a in images:
        #print(a, images[a])
        graph = calculate_graph(tfg, images[a])
        #print(graph)
        withweights = []
        for e in graph:
            withweights.append(e + (1,))
        withweights = tofollprecformat(withweights)
        #print("before init compression", withweights)
        foll, prec, new_loops = compress_wpb_graph(withweights)
        #print("after", foll, prec)
        loops.update(new_loops)
        #print(foll, prec, loops)
        def renaming(x):
            #print("ren", x)
            if x <= rad:
                return ("L", x)
            if len(images[a]) - 1 - x <= rad:
                return ("R", len(images[a]) - 1 - x)
            #raise Exception("something went wrong")
            return None
        foll, prec = rename_vertices((foll, prec), renaming)
        #print("after rename", foll, prec)
        #print(loops)
        structures[a] = foll, prec, images[a][:rad+1], images[a][-rad-1:]
        #print(structures[a])
    # just remembed the topology of graph initially
    passing = True
    seen_structures = set([hashable_structures(structures, passing)])
    while True:
        next_str, new_loops = next_structures(sub, structures, tfg)
        loops = loops.union(new_loops)
        #print(structures)
        new_passing = has_passing(next_str)
        #print(new_passing, "has passing")
        # we no longer have passing, start over
        if passing and not new_passing:
            seen_structures = set([])
        passing = new_passing
        h = hashable_structures(next_str, passing)
        if h in seen_structures:
            if passing:
                return INFINITE
            loops.remove(0)
            return LOOPS, loops
        seen_structures.add(h)

def next_structures(sub, structures, tfg):
    #print("next")
    new_structures = {}
    loops = set()
    for a in sub:
        #print("a",a)
        folla = {}
        preca = {}
        # make a copy of follower & precedessor set in the big one
        for i, b in enumerate(sub[a]):
            foll, prec, pref, suff = structures[b]
            for f in foll:
                img = foll[f]
                folla[f + (i,)] = img[0] + (i,), img[1]
            for f in prec:
                img = prec[f]
                preca[f + (i,)] = img[0] + (i,), img[1]
        #print("kop")
        # add the new edges
        for i in range(len(sub[a]) - 1):
            follL, precL, prefL, suffL = structures[sub[a][i]]
            follR, precR, prefR, suffR = structures[sub[a][i+1]]
            word = suffL + prefR
            for j in range(len(word)):
                #print(j)
                jmp = tfg_jump(tfg, word, j)
                if jmp == None:
                    continue
                #print(jmp, "as")
                if j < len(suffL):
                    if ("R", len(suffL) - 1 - j) in follL: # or ("R", len(suffL) - 1 - j) not in precL:
                        continue
                    if jmp < len(suffL):
                        folla[("R", len(suffL) - 1 - j, i)] = (("R", len(suffL) - 1 - jmp, i), 1)
                        preca[("R", len(suffL) - 1 - jmp, i)] = (("R", len(suffL) - 1 - j, i), 1)
                    else:
                        folla[("R", len(suffL) - 1 - j, i)] = (("L", jmp - len(suffL), i + 1), 1)
                        preca[("L", jmp - len(suffL), i + 1)] = (("R", len(suffL) - 1 - j, i), 1)
                elif j >= len(suffL):
                    reli = j - len(suffL)
                    if ("L", reli) in follR: # or ("L", reli) not in precR:
                        continue
                    
                    if jmp < len(suffL):
                        folla[("L", reli, i + 1)] = (("R", len(suffL) - 1 - jmp, i), 1)
                        preca[("R", len(suffL) - 1 - jmp, i)] = (("L", reli, i + 1), 1)
                    else:
                        folla[("L", reli, i + 1)] = (("L", jmp - len(suffL), i + 1), 1)
                        preca[("L", jmp - len(suffL), i + 1)] = (("L", reli, i + 1), 1)
                #print("comp")
        folla, preca, new_loops = compress_wpb_graph((folla, preca))
        #print(folla, preca)
        loops.update(new_loops)
        #print("whil")
        finalpref = structures[sub[a][0]][2]
        finalsuff = structures[sub[a][-1]][3]
        finalfolla = {}
        finalpreca = {}
        for f in folla:
            to, wt = folla[f]
            #print(f, to)
            #assert f[0] == "L" and f[2] == 0 or f[0] == "R" and f[2] == len(sub[a])-1
            #assert to[0] == "L" and to[2] == 0 or to[0] == "R" and to[2] == len(sub[a])-1
            if (f[0], f[2]) not in [("L", 0), ("R", len(sub[a])-1)]: continue
            if (to[0], to[2]) not in [("L", 0), ("R", len(sub[a])-1)]: continue
            finalfolla[f[:-1]] = to[:-1], wt
        for f in preca:
            to, wt = preca[f]
            if (f[0], f[2]) not in [("L", 0), ("R", len(sub[a])-1)]: continue
            if (to[0], to[2]) not in [("L", 0), ("R", len(sub[a])-1)]: continue
            finalpreca[f[:-1]] = to[:-1], wt
        new_structures[a] = finalfolla, finalpreca, finalpref, finalsuff
    return new_structures, loops

def has_passing(structures):
    for a in structures:
        for k in structures[a][0]:
            if k[0] != structures[a][0][k][0][0]:
                return True
    return False

# return only the form of structure
def hashable_structures(s, only_structure = True):
    ret = {}
    for a in s:
        if only_structure:
            x = erase_weights(s[a][0])
            y = erase_weights(s[a][1])
        else:
            x = s[a][0]
            y = s[a][1]
        ret[a] = fd(x), fd(y), s[a][2], s[a][3]
    return fd(ret)

def erase_weights(d):
    ret = {}
    for a in d:
        ret[a] = d[a][0]
    return ret
    
# rename vertices of weighted graph in follprec format
def rename_vertices(graph, func):
    foll, prec = graph
    retfoll, retprec = {}, {}
    for f in foll:
        if func(f) == None: # these should always be self-loops anyway
            continue
        retfoll[func(f)] = func(foll[f][0]), foll[f][1]
    for f in prec:
        if func(f) == None:
            continue
        retprec[func(f)] = func(prec[f][0]), prec[f][1]
    return retfoll, retprec

# calculate a graph with nodes the position of word, and
# jumps given by tfg element
def calculate_graph(tfg, word):
    edges = []
    for i in range(len(word)):
        j = tfg_jump(tfg, word, i)
        if j != None:
            edges.append((i, j))
    return edges

# from edges to foll and prec sets
def tofollprecformat(edges):
    foll = {}
    prec = {}
    for e in edges:
        foll[e[0]] = (e[1], e[2])
        prec[e[1]] = (e[0], e[2])
    return foll, prec

# compress a weighted partial bijection graph
# also changes format to a pair of dicts...
def compress_wpb_graph(graph):
    #print("compressing", graph)
    foll, prec = graph
    handled = set()
    retfoll = {}
    retprec = {}
    nodes = set()
    for f in foll:
        nodes.add(f)
        nodes.add(foll[f][0])
    loops = set()
    for a in nodes:
        if a in handled:
            continue
        handled.add(a)
        first = a
        last = a
        total = 0
        broke = False
        dat_piece = [first]
        while first in prec:
            total += prec[first][1]
            first = prec[first][0]
            if first == a:
                loops.add(total)
                broke = True
                for k in dat_piece:
                    retfoll[k] = (k, 0)
                    retprec[k] = (k, 0)
                break
            dat_piece.append(first)
            handled.add(first)
        if broke:continue
        while last in foll:
            total += foll[last][1]
            last = foll[last][0]
            dat_piece.append(last)
            if last == a:
                print()
                print(a)
                print(foll)
                print(prec)
                raise Exception("cannot happen")
        for q in dat_piece:
            if q == first or q == last:
                continue
            retfoll[q] = (q, 0)
            retprec[q] = (q, 0)
        retfoll[first] = (last, total)
        retprec[last] = (first, total)
    return retfoll, retprec, loops

def tfg_jump(tfg, word, pos):
    for e in tfg:
        for q in e:
            #print("try", q)
            pa = pattern_applies(q[0], word, pos)
            #print(pa)
            if pa == None:
                return None
            if pa == True:
                pos = pos + q[1]
                if pos < 0 or pos >= len(word):
                    return None
                break
    return pos

def pattern_applies(ptrn, word, pos):
    for t in ptrn:
        relpos = pos + t
        if relpos < 0 or relpos >= len(word):
            return None
        if word[relpos] != ptrn[t]:
            return False
    return True

def iterate_sub_until_lengths(sub, l):
    curr = dict(sub)
    minlen = None
    while True:
        prev = minlen
        curr = compose_substitutions(sub, curr)
        minlen = min(len(curr[i]) for i in curr)
        if prev == minlen:
            raise Exception("Substitution is not growing.")
        if minlen >= l:
            return curr

def compose_substitutions(suba, subb):
    subc = {}
    for a in suba:
        w = suba[a]
        res = ""
        for b in w:
            res += subb[b]
        subc[a] = res
    return subc

def bound_rad(tfg):
    lrad = 0
    rrad = 0
    for a in tfg:
        alrad, arrad = 0, 0
        for q in a:
            alrad = max(alrad, -q[1])
            arrad = max(arrad, q[1])
            for c in q[0]:
                alrad = max(alrad, -c)
                arrad = max(arrad, c)
        lrad += alrad
        rrad += arrad
    return lrad, rrad

def invert_tfg(tfg):
    ret = []
    for l in tfg:
        cond, move = l
        shifted_cond = {}
        for q in cond:
            shifted_cond[q - move] = cond[q]
        ret.append((shifted_cond, -move))
    return ret

#a = [({}, -1)]

# shift right
s = [({}, 1)]

# shift left
S = invert_tfg(s)

# first return map to 0 assuming always dist <= 3
fr0 = [({0 : "0", 1 : "0"}, 1),
     ({0 : "0", 2 : "0"}, 2),
     ({0 : "0", 3 : "0"}, 3)]

# first return map to 1 same assumption
fr1 = [({0 : "1", 1 : "1"}, 1),
     ({0 : "1", 2 : "1"}, 2),
     ({0 : "1", 3 : "1"}, 3)]

TM = {"0" : "01", "1" : "10"}
fib = {"0" : "01", "1" : "0"}

# backward return maps
br1 = invert_tfg(fr1)
br0 = invert_tfg(fr0)

# flip two adjacent 00s
f00 = [({-1 : "1", 0 : "0", 1 : "0", 2 : "1"}, 1),
    ({-2 : "1", -1 : "0", 0 : "0", 1 : "1"}, -1)]

#f11 = [({-1 : "0", 0 : "1", 1 : "1", 2 : "0"}, 1),
#    ({-2 : "0", -1 : "1", 0 : "1", 1 : "0"}, -1)]

a = [fr1, fr1, f00]
A = [f00, br1, br1]
b = [s]
B = [S]
ret = calculate_order(b + a + B + A, fib)
print(ret)


