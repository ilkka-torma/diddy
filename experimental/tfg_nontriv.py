import frozendict
fd = frozendict.FrozenDict
INFINITE = "infinite"
LOOPS = "loops"

def sft_language(sft, n):
    alpha, forbs = sft
    if n == 0:
        yield ""
        return
    for w in sft_language(sft, n-1):
        for a in alpha:
            candidate = a + w
            for f in forbs:
                if candidate[:len(f)] == f:
                    break
            else:
                yield candidate

def extensions_of_all(sft, words):
    for w in words:
        for k in extensions(sft, w):
            yield k

def extensions(sft, w):
    alpha, forbs = sft
    for a in alpha:
        u = a+w
        for f in forbs:
            if u[:len(f)] == f:
                break
        else:
            for b in alpha:
                v = u+b
                for f in forbs:
                    if v[-len(f):] == f:
                        break
                else:
                    yield v
                
def sft_radius(sft):
    m = 0
    for f in sft[1]:
        if len(f) > m:
            m = len(f)
    return m

# given tfg element and substitution, calculate order
def calculate_order(tfg, sft):
    alpha, forbs = sft
    lrad, rrad = bound_rad(tfg)
    rad = max(lrad, rrad)
    rad = max(rad, sft_radius(sft))
    lang = set(sft_language(sft, rad*2+2))
    #print(rad)
    #print(lang)
    #lang = set(["0"])
    structures = set()
    loops = set()
    for word in lang:
        graph = calculate_graph(tfg, word)
        #print(word)
        withweights = []
        for e in graph:
            withweights.append(e + (1,))
        #print(word)
        #print(withweights)
        withweights = tofollprecformat(withweights)
        #print(withweights)
        assert are_inverses(withweights[0], withweights[1])
        foll, prec, new_loops = compress_wpb_graph(withweights)
        assert are_inverses(foll, prec)
        loops.update(new_loops)
        def renaming(x):
            if x <= rad:
                return ("L", x)
            if len(word) - 1 - x <= rad:
                return ("R", len(word) - 1 - x)
            return None
        foll, prec = rename_vertices((foll, prec), renaming)
        assert are_inverses(foll, prec)
        #print("word", word)
        #print(foll)
        structures.add(hashable_structure((foll, prec, word[:rad+1], word[-rad-1:]), False))
    # just remember the topology of graph initially
    passing = True
    # actually now structure is a single thing and this is a set of sets of structures... anyway
    seen_structures = set([frozenset(structures)])
    while True:
        #print("lel")
        next_str, new_loops = next_structures(sft, structures, tfg)
        #print("ke")
        loops = loops.union(new_loops)
        new_passing = has_passing(next_str)
        # we no longer have passing, start over
        if passing and not new_passing:
            seen_structures = set([])
        passing = new_passing
        h = hashable_structures(next_str, passing)
        if h in seen_structures:
            if passing:
                return INFINITE
            loops.discard(0)
            return LOOPS, loops
        seen_structures.add(h)

def in_sft_language(word, sft):
    for a in word:
        if a not in sft[0]:
            return False
    for f in sft[1]:
        for i in range(len(word) - len(f) + 1):
            if word[i:i+len(f)] == f:
                return False
    return True

def are_inverses(a, b):
    for x in a:
        if not (a[x][0] in b and b[a[x][0]][0] == x):
            print(x, a, b)
            return False
    for x in b:
        if not (b[x][0] in a and a[b[x][0]][0] == x):
            print(x, a, b)
            return False
    return True

def next_structures(sft, structures, tfg):
    print(len(structures))
    new_structures = set()
    loops = set()
    for a in structures:
        #print("efwr", len(structures))
        for b in structures:
            follL, precL, prefL, suffL = a
            follR, precR, prefR, suffR = b
            if not in_sft_language(suffL + prefR, sft):
                continue
            folla = {}
            preca = {}
            # make a copy of follower & precedessor set in the big one
            for f in follL:
                img = follL[f]
                folla[f + (0,)] = img[0] + (0,), img[1]
            for f in precL:
                img = precL[f]
                preca[f + (0,)] = img[0] + (0,), img[1]
            for f in follR:
                img = follR[f]
                folla[f + (1,)] = img[0] + (1,), img[1]
            for f in precR:
                img = precR[f]
                preca[f + (1,)] = img[0] + (1,), img[1]

            assert are_inverses(follL, precL)
            assert are_inverses(follR, precR)
            assert are_inverses(folla, preca)

            # add the new edges
            
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
                        folla[("R", len(suffL) - 1 - j, 0)] = (("R", len(suffL) - 1 - jmp, 0), 1)
                        preca[("R", len(suffL) - 1 - jmp, 0)] = (("R", len(suffL) - 1 - j, 0), 1)
                    else:
                        folla[("R", len(suffL) - 1 - j, 0)] = (("L", jmp - len(suffL), 1), 1)
                        preca[("L", jmp - len(suffL), 1)] = (("R", len(suffL) - 1 - j, 0), 1)
                elif j >= len(suffL):
                    reli = j - len(suffL)
                    if ("L", reli) in follR: # or ("L", reli) not in precR:
                        continue
                    
                    if jmp < len(suffL):
                        folla[("L", reli, 1)] = (("R", len(suffL) - 1 - jmp, 0), 1)
                        preca[("R", len(suffL) - 1 - jmp, 0)] = (("L", reli, 1), 1)
                    else:
                        folla[("L", reli, 1)] = (("L", jmp - len(suffL), 1), 1)
                        preca[("L", jmp - len(suffL), 1)] = (("L", reli, 1), 1)

            if not are_inverses(folla, preca):
                print("npo longer are")
                print()
                for q in a:
                    print(q)
                print()
                for q in b:
                    print(q)
                print()
                print("fika us", folla)
                print("aaafika us", preca)
                for q in folla:
                    print(q, folla[q])
                print()
                for q in preca:
                    print(q, preca[q])

            assert are_inverses(folla, preca)

            #print("here")
            folla, preca, new_loops = compress_wpb_graph((folla, preca))
            #print(folla, preca)
            loops.update(new_loops)
            #print("whil")
            finalpref = prefL
            finalsuff = suffR
            finalfolla = {}
            finalpreca = {}
            for f in folla:
                to, wt = folla[f]
                if (f[0], f[2]) not in [("L", 0), ("R", 1)]: continue
                if (to[0], to[2]) not in [("L", 0), ("R",1)]: continue
                finalfolla[f[:-1]] = to[:-1], wt
            for f in preca:
                to, wt = preca[f]
                if (f[0], f[2]) not in [("L", 0), ("R", 1)]: continue
                if (to[0], to[2]) not in [("L", 0), ("R", 1)]: continue
                finalpreca[f[:-1]] = to[:-1], wt
            new_structures.add(hashable_structure((finalfolla, finalpreca, finalpref, finalsuff), False))
    return new_structures, loops

def has_passing(structures):
    for a in structures:
        for k in a[0]:
            if k[0] != a[0][k][0][0]:
                return True
    return False

# s is now a set of structures
# return only the form of structure, maybe
def hashable_structures(s, only_structure):
    ret = set()
    for a in s:
        ret.add(hashable_structure(a, only_structure))
    return frozenset(ret)

def hashable_structure(s, only_structure):
    if only_structure:
        x = erase_weights(s[0])
        y = erase_weights(s[1])
    else:
        x = s[0]
        y = s[1]
    return (fd(x), fd(y), s[2], s[3])


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
def compress_wpb_graph(graph, word = None):
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
                print(word)
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
    #print("jump", word, pos)
    for e in tfg:
        #print(e, "onesdf", pos)
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

def nontrivial(tfg, sft):
    lrad, rrad = bound_rad(tfg)
    rad = max(lrad, rrad)
    rad = max(rad, sft_radius(sft))
    lefts = None # ones we didn't handle yet
    for q in range(1, rad + 10):
        
        if lefts == None:
            lefts = set(sft_language(sft, q*2+1))
        #print(q, "len", lefts)
        newlefts = set()
        for w in extensions_of_all(sft, lefts):
            #print(w, "trying")
            j = tfg_jump(tfg, w, q)
            #print("jump", j, rad, tfg)
            if j == None:
                newlefts.add(w)
                continue
            if j != q:
                return True
        #print(len(newlefts))
        if len(newlefts) == 0:
            return False
    
        lefts = newlefts

    raise Exception("s")
    


#a = [({}, -1)]
id = [({}, 0)]

# shift right
s = [({}, 1)]

# shift left
S = invert_tfg(s)

golden = (["0", "1"], ["11"])

adr_sft = (["0", "1", "2"], ["21", "00", "02", "11"])

a = [({0 : "0"}, 2),
         ({0 : "1"}, 0),
         ({0 : "2"}, 1),]

b = [({0 : "0"}, 0),
         ({0 : "1"}, 1),
         ({0 : "2", 1 : "0"}, 2),
         ({0 : "2", 1 : "2"}, 1),]


A = invert_tfg(a)
B = invert_tfg(b)

def fwords(gens, n):
    if n == 0:
        yield ""
        return
    for f in fwords(gens, n-1):
        for g in gens:
            for G in [g, g.upper()]:
                if f == "" or (G.lower() != f[0].lower() or G == f[0]):
                #if True:
                    yield G + f


#print(tfg_jump([a, A], "222", 1))
#print([a, A])

#a = bbb
for r in range(1, 20):
    print(r)
    for w in fwords(["a", "b"], r):
        # print(w)
        elem = []
        for q in w:
            if q == "a":
                elem.append(a)
            if q == "A":
                elem.append(A)
            if q == "b":
                elem.append(b)
            if q == "B":
                elem.append(B)
        #print(w)
        ret = nontrivial(elem + elem + elem, adr_sft)
        #print("nontrivial?", w, ret)
        if not ret:
            print(w)
    #break






