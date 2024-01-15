from circuit import *
from general import *
from sft import *
import mocircuits
import time


"""
circuits is a dict of circuits : (node, symbol) -> circuit
for each node exactly one should say yes or this is nondeterministic
variables in circuits are (vector, node, symbol) encodeed
overlaps should be "ignore", "check" or "remove"
"""
class BlockMap:
    def __init__(self, from_alphabet, to_alphabet, from_nodes, to_nodes, dimension, circuits, from_topology, to_topology, overlaps="remove", verbose=False):
        self.from_alphabet = from_alphabet
        self.to_alphabet = to_alphabet
        self.from_nodes = from_nodes
        self.to_nodes = to_nodes
        self.dimension = dimension
        self.from_topology = from_topology
        self.to_topology = to_topology

        #assert type(circuits) == dict

        #  dict is only used internally, assume disjointness and full specification
        if type(circuits) == dict:
            self.circuits = circuits #[(n,a,circuits[(n,a)]) for (n,a) in circuits]

        # inputs can be messier, and we remove intersections and add defaults
        # by default, default is first missing symbol, or first letter of alphabet
        # if all appear...
        if type(circuits) == list:
            
            self.circuits = self.circuits_from_list(circuits, overlaps)

            for n in to_nodes:
                circs = {}
                for a in to_alphabet[n]:
                    if (n, a) in self.circuits:
                        circs[a] = self.circuits[(n, a)]
                # check if we should add default case because one is explicitly missing
                if len(circs) < len(to_alphabet[n]):
                    default_found = False
                    for a in to_alphabet[n]:
                        if a not in circs:
                            if not default_found:
                                if verbose:
                                    print("Using {} as default symbol for node {} in block map".format(a, n))
                                self.circuits[(n, a)] = AND(*(NOT(b) for b in circs.values()))
                            else:
                                self.circuits[(n, a)] = F
                # all formulas are there, but we should possibly still add a default case
                # if it's possible that no formula triggers; default is first letter then
                else:
                    ldac = LDAC2(self.from_alphabet)
                    first_sym = from_alphabet[n][0]
                    if SAT_under(AND(*(NOT(b) for b in circs.values())), ldac):
                        if verbose:
                            print("Using {} as default symbol for node {} in block map".format(first_sym, n))
                        self.circuits[(n, first_sym)] = AND(*(NOT(circs[b]) for b in circs if b != first_sym))

    # we get a list of (node, sym, formula)
    # if overlaps is "remove", we should refine to disjoints:
    # if (n, a, C) appears, and (n, b) already has formula,
    # then, remove simultaneous solutions from C
    # if overlaps is "check", we should raise an exception if the rules are not disjoint
    # if overlaps if "ignore", assume the rules are disjoint
    def circuits_from_list(self, circuits, overlaps):
        if overlaps == "ignore":
            disjoints = circuits
        else:
            disjoints = []
            for (node, sym, formula) in circuits:
                form = formula
                # go over all previous
                for (node_, sym_, formula_) in disjoints:
                    if node_ != node:
                        continue
                    if sym_ != sym:
                        #print("from_alphabet", self.from_alphabet)
                        ldac = LDAC2(lambda nvec: self.from_alphabet[nvec[-1]])
                        if SAT_under(AND(form, formula_), ldac):
                            if overlaps == "check":
                                raise Exception("Overlapping rules for node {}, symbols {} and {}".format(node_, sym_, sym))
                            form = AND(form, NOT(formula_))
                disjoints.append((node, sym, form))
        ret_circuits = {}
        for (node, sym, formula) in disjoints:
            if (node, sym) not in ret_circuits:
                ret_circuits[(node, sym)] = formula
            else:
                ret_circuits[(node, sym)] = OR(ret_circuits[(node, sym)], formula)
        return ret_circuits

    def tomocircuit(self):
        return mocircuits.MOCircuit(self.circuits)

    # compose with other; other is done after
    def then(self, other):
        assert self.to_alphabet == other.from_alphabet
        assert self.to_nodes == other.from_nodes
        assert self.dimension == other.dimension

        # calculate all cells that will be used
        other_cells = set()
        for c in other.circuits:
            for s in other.circuits[c].get_variables():
                other_cells.add(s[:-2]) # just need to know the shifts
                
        # Make shifted copies of our circuits, one for each cell used by other.
        # Note that the circuits that do not get used are actually killed by
        # Python's GC, because they are literally not going to be involved in
        # the final circuit.
        circuits = {}
        for s in other_cells: # ns = node, symbol
            for ns in self.circuits:
                circuit_copy = self.circuits[ns].copy()
                def shift(v):
                    return vadd(v[:-2], s) + v[-2:]
                #print("transforming")
                #print(circuit_copy, s)
                transform(circuit_copy, shift)
                #print(circuit_copy)
                circuits[s + ns] = circuit_copy

        # now the circuits dict has for each relevant position-symbol combo a circuit
        # we just combine them with the other circuit by literally replacing

        ret_circuits = {}
        for ns in other.circuits: # ns = node, symbol
            # we should construct the circuit for a particular node and symbol
            # make a copy of the relevant circuit
            ret_circuit = other.circuits[ns].copy()
            # ns = node, symbol
            transform(ret_circuit, lambda a:circuits[a])
            ret_circuits[ns] = ret_circuit

        ret = BlockMap(self.from_alphabet, other.to_alphabet, self.from_nodes, other.to_nodes, self.dimension, ret_circuits, self.from_topology, other.to_topology)
        return ret

    def after(self, other):
        return other.then(self)

    def __eq__(self, other):
        if self.from_alphabet != other.from_alphabet:
            return False
        if self.to_alphabet != other.to_alphabet:
            return False
        if self.dimension != other.dimension:
            return False
        if self.from_nodes != other.from_nodes:
            return False
        if self.to_nodes != other.to_nodes:
            return False
        #print("he")
        for ns in self.circuits:
            #print(ns)
            ldac = LDAC2(self.from_alphabet) #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            if not equivalent_under(self.circuits[ns], other.circuits[ns], ldac):
                return False
        return True

    def separating(self, other):
        "Return a witness for inequality, or None if one does not exist"
        for ns in self.circuits:
            #print(ns)
            ldac = LDAC2(self.from_alphabet) #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            diff = equivalent_under(self.circuits[ns], other.circuits[ns], ldac, return_sep=True)
            if diff != True:
                pat = dict()
                domain = set(var[:-2] for var in diff)
                for vec in domain:
                    for node in self.from_nodes:
                        for sym in self.from_alphabet[node][1:]:
                            if diff.get(vec+(node,sym), False):
                                pat[vec+(node,)] = sym
                                break
                        else:
                            pat[vec+(node,)] = self.from_alphabet[node][0]
                return (ns, pat)
        return None

    def injective_to_ball(self, r):
        # two circuits per position per letter
        # force images same
        # force preimage different
        eq_circuits = []
        for p in centered_hypercube(self.dimension, r):
            for n in self.to_nodes:
                for a in self.to_alphabet:
                    circA = self.circuits[(n, a)].copy()
                    circB = self.circuits[(n, a)].copy()
                    # shift the cell, i.e. not node or letter
                    # and also add x at the end, we make two copies of each
                    def shift(v, x): return vadd(v[:-2], p) + v[-2:] + (x,)
                    transform(circA, lambda y:shift(y, "A"))
                    #circuits[p + (n, a, 0)] = circA
                    transform(circB, lambda y:shift(y, "B"))
                    #circuits[p + (n, a, 1)] = circB
                    eq_circuits.append(IFF(circA, circB))
                    #print(IFF(circA, circB))
                    
        origin = (0,)*self.dimension
        differents = []
        for n in self.from_nodes:
            for a in self.from_alphabet:
                differents.append(XOR(V(origin + (n, a, "A")), V(origin + (n, a, "B"))))
        # all images must be the same, and some central node has diff preimage
        ret = UNSAT_under(AND(AND(*eq_circuits), OR(*differents)), LDAC2(self.from_alphabet))

        return ret
        
    def __repr__(self):
        return repr(self.circuits)

    """
    A CA is injective on its full shift if there exists
    a radius r such that there do not exist a pair of
    r-sized patterns P, Q with distinct central symbols which have
    distinct images.

    On the other hand, it is not injective if we can find two periodic
    points with the same image.
    """
    def injective(self):
        r = 1
        while True:
            if self.injective_to_ball(r):
                return True
            if not self.injective_on_periodics(r):
                return False
            r += 1

    # assume the environments match
    def preimage(self, the_sft):
        sft_circ = the_sft.circuit.copy()
        for var in sft_circ.get_variables():
            substitute(sft_circ, var, V(var+(None,))) # prevent accidental repeated substitutions
        for var in sft_circ.get_variables():
            vec, node, sym = var[:-3], var[-3], var[-2]
            bm_circ = self.circuits[node, sym].copy()
            transform(bm_circ, lambda var2: vadd(vec, var2[:-2]) + var2[-2:])
            substitute(sft_circ, var, bm_circ)
        return SFT(self.dimension, self.from_nodes, self.from_alphabet, self.from_topology, circuit=sft_circ)

    def relation(self, tracks=None):
        "The relation defining this block map (as an SFT), i.e. its graph"
        if tracks is None:
            tracks = (0,1)
        dom_alph = self.from_alphabet
        dom_nodes = self.from_nodes
        cod_alph = self.to_alphabet
        cod_nodes = self.to_nodes
        dim = self.dimension
        nodes = Nodes({tr:nodes for (tr, nodes) in zip(tracks, (dom_nodes, cod_nodes))})
        alph = {add_track(tr,node) : alph[node]
                for (tr, nodes, alph) in zip(tracks, (dom_nodes, cod_nodes), (dom_alph, cod_alph))
                for node in nodes}
        anded = []
        for ((node, sym), circ) in self.circuits.items():
            new_circ = circ.copy()
            transform(new_circ, lambda var: var[:-2] + (add_track(tracks[0], var[-2]),) + var[-1:])
            if sym != cod_alph[node][0]:
                anded.append(IFF(V((0,)*dim + (add_track(tracks[1],node), sym)), new_circ))
            else:
                not_others = AND(*(NOT(V((0,)*dim + (add_track(tracks[1],node), sym2))) for sym2 in cod_alph[node][1:]))
                anded.append(IFF(not_others, new_circ))
                
        #for sft in sfts:
        #    print(sft)
        #    print("topo", sft.topology)
        #    print()
        topology = []
        for tr in tracks:
            if tr == tracks[0]:
                topo = self.from_topology
            else:
                topo = self.to_topology
            for t in topo:
                # t[:1] is the name of an edge. We make a copy with track added.
                topology.append(t[:1] + tuple(vec[:-1] + (add_track(tr, vec[-1]),) for vec in t[1:]))
        #print(topology)
        
        return SFT(dim, nodes, alph, topology, circuit=AND(*anded))

    def is_CA(self):
        return self.to_alphabet == self.from_alphabet and self.to_nodes == self.from_nodes # and self.to_topology == self.from_topology

    def fixed_points(self):
        "The SFT of fixed points of this CA"
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        anded = []
        for ((node, sym), circ) in self.circuits.items():
            new_circ = circ.copy()
            if sym != alph[node][0]:
                anded.append(IMP(V((0,)*dim + (node, sym)), new_circ))
            else:
                not_others = AND(*(NOT(V((0,)*dim + (node, sym2))) for sym2 in alph[node][1:]))
                anded.append(IMP(not_others, new_circ))
        return SFT(dim, nodes, alph, self.from_topology, circuit=AND(*anded))

    def spacetime_diagram(self, onesided=True, time_axis=None):
        "The SFT of spacetime diagrams of this CA"
        assert self.is_CA()
        alph = self.from_alphabet
        nodes = self.from_nodes
        dim = self.dimension
        
        if time_axis is None:
            time_axis = self.dimension

        anded = []
        for ((node, sym), circ) in self.circuits.items():
            new_circ = circ.copy()
            transform(new_circ, lambda var: var[:time_axis] + (0,) + var[time_axis:])
            val_vec = (0,)*time_axis + (1,) + (0,)*(dim-time_axis) + (node,)
            local_alph = alph[node]
            if sym == local_alph[0]:
                is_val = AND(*(NOT(V(val_vec + (sym2,))) for sym2 in local_alph[1:]))
            else:
                is_val = V(val_vec + (sym,))
            anded.append(IFF(new_circ, is_val))

        #print(self.from_topology)

        topology = []
        for t in self.from_topology:
            # append the new dimension in the edges
            topology.append(t[:1] + tuple(tt[:time_axis] + (0,) + tt[time_axis:] for tt in t[1:]))
            # add the time direction, default name is "fut"
        for  n in nodes:
            topology.append(("fut", (0,)*(dim+1) + (n,), (0,)*time_axis + (1,) + (0,)*(dim-time_axis) + (n,)))
            topology.append(("past", (0,)*time_axis + (1,) + (0,)*(dim-time_axis) + (n,), (0,)*(dim+1) + (n,)))
            
        return SFT(dim+1, nodes, alph, topology, circuit=AND(*anded), onesided=[time_axis] if onesided else [])

    # pattern is just a dictionary from vectors to tuple of letters, we evaluate at origin
    #def evaluate_on_explicit(pattern):
    #    ...

    def get_neighborhood(self, only_cells):
        if not only_cells :
            raise Exception("Neighborhood in terms of nodes not implemented.")
        circs = self.circuits
        neighborhood = set()
        for n in nodes:
            for s in from_alph[n]:
                for q in circs[n, s].get_variables():
                    vec, n, s = q[:-2], q[-2], q[-1]
                    neighborhood.add(vec)
        return neighborhood

    def local_rule(self, pattern):
        img_sym = ()
        for n in self.from_nodes:
            for a in self.from_alphabet[n]:
                

    """
    def explicit_local_rule(self, contiguous = False):
        if contiguous:
            if self.dimension != 1:
                raise Exception("Contiguous local rule can only be requested in one dimension.")
            
        from_nodes = self.from_nodes
        from_alph = self.from_alphabet # this is a dict from nodes to alphabets
        # circuits are a dictionary from node and symbol to circuit telling us when it is accepting
        circs = self.circuits

        # first, calculate the neighborhood
        neighborhood = []
        for n in nodes:
            for s in from_alph[n]:
                for q in circs[n, s].get_variables():
                    vec, n, s = q[:-2], q[-2], q[-1]
                    neighborhood.append(vec)
                    
        if contiguous:
            # dimension is 1, note that we have singleton tuples but they compare the same
            m, M = min(neighborhood), max(neighborhood)
            neighborhood = [(s,) for s in range(m[0], M[0]+1)]
            
        #if open_singleton_tuple:
        #    neighborhood = [s[0] for s in neighborhood]
            
        # next, the main part: calculate the rule as an explicit local rule
        # for each node, we should enumerate all possible patterns in the neighborhood
        nodepats = list()
        for n in nodes:
            nodepats.append(pats(neighborhood, from_alph[n]))
        
        rule = {}
        for c in iter_prod(*nodepats):
            # transpose the product so that it's from vectors to product alphabet
            ptrn = {}
            for v in neighborhood:
                ptrn[v] = [cc[v] for cc in c]
            result = self.evaluate_on(ptrn)
    """

    def local rule(self):

# given a list of cellular automata, compute relations
# among them up to radius rad as semigroup
def find_relations(CAs, rad):
    i = 0
    firstCA = CAs[0]
    alphabet = firstCA.to_alphabet
    nodes = firstCA.to_nodes
    dimension = firstCA.dimension
    indices = []
    for n in nodes:
        for a in alphabet[n]:
            indices.append((n, a))
    mod = mocircuits.MOCircuitDict(indices)
    identityrule = {}
    for n in nodes:
        for a in alphabet[n][1:]:
            identityrule[(n, a)] = V((0,)*dimension + (n, a))
    # topology None because it really does not matter
    idca = BlockMap(alphabet, alphabet, nodes, nodes, dimension, identityrule, None, None)
    #assert idca.then(idca) == idca
    mod[idca.tomocircuit()] = (idca, ())
    #print("idcirc", idca.circuits)
    #print("cacirc", CAs[0].circuits)
    

    #print(CAs[0])

    #assert CAs[0].tomocircuit() in mod
    
    #a = bbb
    frontier = [(idca, ())]

    
    #assert idca.tomocircuit() in mod
    """
    for i in range(len(CAs)):
        if CAs[i].tomocircuit() not in mod:
            mod[CAs[i].tomocircuit()] = (CAs[i], (i,))
            frontier.append((CAs[i], (i,)))
            yield
    """

    relations = []
    for r in range(rad):
        print("Frontier size %s at depth %s; total number of CA %s." % (len(frontier), r, len(mod)))
        #for ca, w in frontier:
        #    print(w)
        newfrontier = []
        for ca, w in frontier:
            for k in range(len(CAs)):
                newca = ca.after(CAs[k])
                newcamo = newca.tomocircuit()
                if newcamo in mod:
                    yield ("rel", mod[newcamo][1], w + (k,))
                    relations.append((mod[newcamo][1], w + (k,)))
                    continue
                yield ("CA", newca, w + (k,))
                mod[newcamo] = (newca, w + (k,))
                newfrontier.append((newca, w + (k,)))
        frontier = newfrontier

    ret = {}
    for k in mod:
        img = mod[k]
        ret[img[1]] = img[0]

    return ret, relations
        
        





#def that_action(CA):
    


#def CA()

"""
Given a cellular automaton, which is a tuple
(alphabet, radius rule)
return a new CA
(alphabet^2 \cup \{>, <\}, new radius, new rule)
which realizes the action from my paper.
"""

# basic testing, id, not, xors

alphabet = {0 : [0, 1]}
nodes = [0]
dimension = 1
id_CA_circuits = {(0,0) : NOT(V((0,0,0,1))), (0,1) : V((0,0,0,1))}
a = BlockMap(alphabet, alphabet, nodes, nodes, dimension, id_CA_circuits, None, None)
print(a.explicit_local_rule(contiguous = True))

"""

not_CA_circuits = {(0,1) : V((0,0,0,0))}
b = CA(alphabet, nodes, dimension, not_CA_circuits)

print(a.then(b) == b, True) # true
print(b.then(b) == a, True) # true
print(b.then(a.then(b)) == b.then(a).then(a), False) # false
print(a.then(b) == b.then(b).then(b), True)


xor_CA_circuits = {(0,1) : XOR(V((0,0,0,1)), V((1,0,0,1)))}
x = CA(alphabet, nodes, dimension, xor_CA_circuits)

xor2_CA_circuits = {(0,1) : XOR(V((0,0,0,1)), V((2,0,0,1)))}
x2 = CA(alphabet, nodes, dimension, xor2_CA_circuits)

print(x.then(x.then(x2).then(a)) == x2.then(x).then(x), True)
print(x.then(x.then(x2)) == x2.then(a).then(x).then(x2), False)
"""



"""
# more interesting testing: lamplighter group; 
alphabet = [0,1]
nodes = ["up", "dn"]
dimension = 1

can = {}
partial_right_shift_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                             ("up", 0) : V((-1,0,"up",0))}
can["R"] = CA(alphabet, nodes, dimension, partial_right_shift_CA_circuits)
partial_left_shift_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                             ("up", 0) : V((1,0,"up",0))}
can["L"] = CA(alphabet, nodes, dimension, partial_left_shift_CA_circuits)
sum_down_CA_circuits = {("up", 0) : V((0,0,"up",0)),
                        ("dn", 1) : XOR(V((0,0,"up",1)), V((0,0,"dn",1)))}
can["s"] = CA(alphabet, nodes, dimension, sum_down_CA_circuits)
id_CA_circuits = {("dn", 0) : V((0,0,"dn",0)),
                  ("up", 0) : V((0,0,"up",0))}
can["e"] = CA(alphabet, nodes, dimension, id_CA_circuits)

def evalstr(s):
    #print(s)
    ret = can["e"]
    for i in s:
        #print(can[i].circuits)
        ret = ret.then(can[i])
    #print(ret, "RETURN")
    return ret

""
print(evalstr("ss") == evalstr("e"), True)
print(evalstr("LR") == evalstr("RL"), True)
print(evalstr("LR") == evalstr("R"), False)
print(evalstr("RRRsLLLsRRRsLLLs") == evalstr("e"), True)
print(evalstr("RRRsLLLsRRRLLLs") == evalstr("e"), False)
""

#CAs, rels = find_relations([can["L"], can["R"], can["s"]], 10)

"""


"""
SO_XOR_circuits = {("up",1) : V((0,"dn",1)),
                   ("dn",1) : XOR(V((0,"dn",1)), V((0,"up",1)), V((1,"up",1)))}
SO_XOR = CA(alphabet, nodes, dimension, SO_XOR_circuits)
#xor_CA_circuits = {(0,"up") : XOR(V((0,0,0,1)), V((1,0,0,1)))}
#x = CA(alphabet, nodes, dimension, xor_CA_circuits)

print(evalstr("RRRsLLLsRRRsLLLs").then(SO_XOR).injective_to_ball(0))
"""

"""

def addat(n):
    if n > 0:
        return "R"*n + "s" + "L"*n
    n = -n
    return "L"*n + "s" + "R"*n

def addats(ns):
    r = ""
    for n in ns:
        r += addat(n)
    return r

t = time.time()
A = evalstr(addats([0, 6, 3, 2, 3]))
B = evalstr(addats([6, 2, 2, 3, 2, 3, 0]))
C = evalstr(addats([6, 5, 4, 3, 2, 1, 0, -1, 5, 4, 3, 1, -1]))
D = evalstr(addats([0, 6, 4, 2, 3]))
print(A == B)
print(B == C)
print(C == D)
#print(evalstr("RRRsLLLsRRRsLLLsL") == evalstr("L"), True)

print(time.time() - t)                        
"""
                        



"""
alphabet = [0,1]
nodes = [0,1]
dimension = 1

#shift_CA_circuits = {(0,1) : XOR(V((0,0,0)), V((1,0,0)))}

# second order xor
#SO_XOR_circuits = {(0,1) : V((0,1,1)),
#                   (1,1) : XOR(V((0,1,1)), V((0,0,1)), V((1,0,1)))}
#a = CA(alphabet, nodes, dimension, SO_XOR_circuits)
#print(a.injective_to_ball(0))
#print(a.injective_to_ball(1))
"""



"""
alphabet = [0,1]
nodes = [0]
dimension = 1

c = {(0,1) : XOR(V((0,0,1)), V((1,0,1)))}
x1 = CA(alphabet, nodes, dimension, c)
c = {(0,1) : XOR(V((0,0,1)), V((1,0,1)), V((2,0,1)))}
x2 = CA(alphabet, nodes, dimension, c)
CAs, rels = find_relations([x1, x2], 7)
"""











