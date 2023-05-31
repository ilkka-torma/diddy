from circuit import *
from general import *
from sft import *
import mocircuits
import time

"""
circuits is a dict of circuits : (node, symbol) -> circuit
for each node exactly one should say yes or this is nondeterministic
variables in circuits are (vector, node, symbol) encodeed
"""
class BlockMap:
    def __init__(self, from_alphabet, to_alphabet, from_nodes, to_nodes, dimension, circuits):
        self.from_alphabet = from_alphabet
        self.to_alphabet = to_alphabet
        self.from_nodes = from_nodes
        self.to_nodes = to_nodes
        self.dimension = dimension

        assert type(circuits) == dict
            
        self.circuits = circuits
        for n in to_nodes:
            circs = {}
            for a in to_alphabet[n]:
                if (n, a) in self.circuits:
                    circs[a] = self.circuits[(n, a)]
            # check if we should add default case
            if len(circs) < len(to_alphabet):
                default_found = False
                for a in to_alphabet[n]:
                    if a not in circs:
                        if not default_found:
                            self.circuits[(n, a)] = AND(*(map(lambda b:NOT(b), circs.values())))
                        else:
                            self.circuits[(n, a)] = F

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

        ret = BlockMap(self.from_alphabet, other.to_alphabet, self.from_nodes, other.to_nodes, self.dimension, ret_circuits)
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
            ldac = LDAC(self.from_alphabet) #lambda a: last_diff_and_count(a, len(self.to_alphabet))
            if not equivalent_under(self.circuits[ns], other.circuits[ns], ldac):
                return False
        return True

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
        # all iamges must be the same, and some central node has diff preimage
        ret = UNSAT_under(AND(AND(*eq_circuits), OR(*differents)), LDAC(self.from_alphabet))

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
        
class CA(BlockMap):
    def __init__(self, alphabet, nodes, dimension, circuits):
        super().__init__(alphabet, alphabet, nodes, nodes, dimension, circuits)

    def spacetime_diagram(self, onesided=True, time_axis=None):
        "The SFT of spacetime diagrams of this CA"
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
            
        return SFT(dim+1, nodes, alph, circuit=AND(*anded), onesided=[time_axis] if onesided else [])
        

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
        for a in alphabet:
            indices.append((n, a))
    mod = mocircuits.MOCircuitDict(indices)
    identityrule = {}
    for n in nodes:
        for a in alphabet[1:]:
            identityrule[(n, a)] = V((0,)*dimension + (n, a))
    idca = CA(alphabet, nodes, dimension, identityrule)
    #assert idca.then(idca) == idca
    mod[idca.tomocircuit()] = (idca, ())
    #print(idca.circuits)
    #print(CAs[0].circuits)


    #print(CAs[0])

    assert CAs[0].tomocircuit() in mod
    
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

"""
alphabet = [0,1]
nodes = [0]
dimension = 2

id_CA_circuits = {(0,0) : V((0,0,0,0))}
a = CA(alphabet, nodes, dimension, id_CA_circuits)

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











