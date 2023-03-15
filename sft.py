
from circuit import *

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

def Z2onesidedsquare(rad):
    for x in range(0, rad):
        for y in range(0, rad):
            yield (x, y)

# check that circuit is forced to be true when variable set
def forced_by(circuit, vals_as_list):
    andeds = []
    for (var, val) in vals_as_list:
        if val:
            andeds.append(V(var))
        else:
            andeds.append(NOT(V(var)))
    return models(andeds, circuit)

# we have a circuit and some values
# minimize the dict of values so that stays tautology
def minimize_solution(circuit, vals, necessary_vals = None):
    
    if necessary_vals == None:
        assert evaluate(circuit, vals)
        necessary_vals = []

    assert type(vals) == dict
    vals = list(vals.items())
    mini = minimize_solution_(circuit, vals, necessary_vals)
    as_dict = {}
    for (var, val) in mini:
        as_dict[var] = val
    return as_dict
        

def minimize_solution_(circuit, vals, necessary_vals):
    #print("juli", vals, necessary_vals)
    if len(vals) == 0:
        return necessary_vals

    first, rest = vals[0], vals[1:]
    if forced_by(circuit, rest + necessary_vals):
        return minimize_solution_(circuit, rest, necessary_vals)

    return minimize_solution_(circuit, rest, necessary_vals + [first])

class SFT:
    "Two-dimensional SFT on a gridlike graph"

    def __init__(self, dim, nodes, alph, forbs=None, circuit=None):
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        self.forbs = forbs
        self.circuit = circuit
        if self.circuit is None:
            self.deduce_circuit()

    def __str__(self):
        return "SFT(dim={}, nodes={}, alph={})".format(self.dim, self.nodes, self.alph)

    # find periodic configuration in c1 which is not in c2
    def exists_periodic_not_in(self, other, r):
        #print("exper", r)
        assert len(self.alph) == 2

        c1 = self.circuit.copy()
        c2 = other.circuit.copy()
        #print(c1)
        #print(c2)
        circuits = {}

        for v in Z2onesidedsquare(r):
            #print(v, "vee")
            circuits[v] = c1.copy()

            for var in c1.get_variables():
                #print(var, "to", vmod(r, vadd(v, var[:-1])) + (var[-1], 0) )
                rel_pos = vmod(r, vadd(v, var[:-1])) + (var[-1], 0)
                #print(var, rel_pos)
                substitute(circuits[v], var, V(rel_pos))
                #print(circuits[v])

        circuits[None] = NOT(c2)
        #print("init", circuits[None])
        for var in c2.get_variables():
            #print("c2", var, "to", V(vmod(r, var[:-1]) + (var[-1], 0)))
            #print("cee", var, vmod(r, var[:-1]) + (var[-1], 0))
            substitute(circuits[None], var, V(vmod(r, var[:-1]) + (var[-1], 0)))
            #print(circuits[None])

        #for k in circuits:
        #    print(k, circuits[k])
        #print("no22")
        m = SAT(AND(*(list(circuits.values()))), True)
        #print(AND(*(list(circuits.values()))))
        if m == False:
            return False
        print(m)
        return True

    def ball_forces_allowed(self, other, r):
        assert len(self.alph) == 2

        circuits = {}

        for v in Z2square(r):
            circuits[v] = self.circuit.copy()
            for var in self.circuit.get_variables():
                rel_pos = vadd(v, var[:-1]) + (var[-1], 0)
                substitute(circuits[v], var, V(rel_pos))
                #print(rel_pos)

        circuits[None] = NOT(other.circuit.copy())
        for var in other.circuit.get_variables():
            substitute(circuits[None], var, V(var + (0,)))

        #print("no22")
        m = SAT(AND(*(list(circuits.values()))))
        if m == False:
            return True
        return False

    def deduce(self, known_values, domain):
        if self.alph != [0,1]:
            raise Exception("Only binary alphabets supported in deduce")
        if not (self.deftype & SFTType.CIRCUIT):
            raise Exception("SFT must have a circuit in deduce")
        
        circuits = {}
    
        for v in domain:
            circuits[v] = circuit.copy()
            for var in circuit.get_variables():
                # translate and add 0 at end so that we don't replace twice
                rel_pos = vadd(v, var[:-1]) + (var[-1], 0) 
                substitute(circuits[v], var, V(rel_pos))
                # print(circuits[v])

        forceds = set()
        for v in known_values:
            if known_values[v] == self.alph[1]:
                forceds.add(V(v + (0,)))
            else:
                forceds.add(NOT(V(v + (0,))))

        #print("no22")
        m = SAT(AND(*(list(circuits.values()) + list(forceds))), True)
        if m == False:
            return None
        #print(m)
        mm = {}
        for v in domain:
            for n in nodes:
                if v + (n, 0) in m:
                    mm[v + (n,)] = m[v + (n, 0,)]
                else:
                    mm[v + (n,)] = None # was not actually discussed by rules
        return mm

    def deduce_circuit(self):
        if self.circuit is None:
            anded = []
            for forb in self.forbs:
                anded.append(OR(*((NOT(V(nvec)) if c else V(nvec)) for (nvec, c) in forb.items())))
            self.circuit = AND(*anded)

    def deduce_forbs(self, domain=None):
        if self.forbs is None:
            self.forbs = []
        if type(domain) == int:
            domain = [vec + (node,) for vec in Z2square(domain) for node in self.nodes]
        if domain is None:
            domain = list(self.circuit.get_variables())
        assert len(self.alph) == 2
        assert all(v in domain for v in self.circuit.get_variables())

        # we want to tile domain so that it has no existing forbos, but
        # the circuit fails at the origin
        complemented = NOT(self.circuit.copy())

        forbiddens = []
        for f in self.forbs:
            # anchor is just some position in domain of forbo (without node info)
            # which we will position in various places
            anchor = list(f)[0][:-1]
            for v in domain:
                for t in f:
                    if vadd(vsub(t[:-1], anchor), v) not in domain:
                        continue
                # we go here if the entire forbidden pattern translate fits in domain
                else:
                    # we make a circuit that says the we differ from the pattern somewhere
                    oreds = []
                    for t in f:
                        u = vadd(v, vsub(t[:-1], anchor)) + (t[-1],)
                        value = f[t]
                        if value == self.alph[1]:
                            oreds.append(NOT(V(u)))
                        else:
                            oreds.append(V(u))
                    forbiddens.append(OR(*oreds))

        m = SAT(AND(complemented, *forbiddens), True)
        if m == False:
            return None

        # we now know that m is a forbidden thingy
        # we then try to minimize it...
        minimal = {}
        for v in complemented.get_variables():
            minimal[v] = m[v]
        #print("minimizing", minimal)
        minimal = minimize_solution(complemented, minimal)
        #a = bbb

        # print("new minimal", minimal)

        self.forbs.append(minimal)
        self.deduce_forbs(domain)

    def contains(self, other, limit = None, return_radius = False):
        r = 1
        while limit is None or r <= limit:
            if other.ball_forces_allowed(self, r):
                if return_radius:
                    return True, r
                return True
            if other.exists_periodic_not_in(self, r):
                if return_radius:
                    return False, r
                return False
            r += 1
        return None

    def equals(self, other, limit = None, return_radius = False):
        c12, rad = self.contains(other, limit, return_radius = True)
        if c12 == None:
            return None, limit
        elif c12 == False:
            return False, rad
        c21, rad2 = other.contains(self, limit, return_radius = True)
        if c21 == None:
            return None, limit
        return c21, max(rad, rad2)
