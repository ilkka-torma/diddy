"""
A CantorPartition object is a continuous function from the
Cantor space on Python objects to Python objects (as a discrete space).
"""

from circuit import T, LDAC2, V, OR, AND, NOT, UNSAT_under, Circuit

class CantorPartition:
    # by default, None everywhere
    def __init__(self, alphabet_func = None, default = None):
        self.default = default
        if default != None:
            self.d = {default : T}
        else:
            self.d = {}
        self.alphabet_func = alphabet_func
        
    def __setitem__(self, key, val):
        #print("setting", key, "to", val)
        assert type(key) == Circuit
        if val in self.d:
            #print(val, "in", self.d)
            self.d[val] = OR(self.d[val], key)
        else:
            #print("herm")
            self.d[val] = key
        #print("sotten")
        for v in self.d:
            if v != val:
                self.d[v] = AND(self.d[v], NOT(key))

    #def __getitem__(self, key):
    #    for v in self.d:

    def apply(self, op, *params):
        #print("applying")
        cart = cartesian_product((self,) + params)
        #print("card")
        #print(cart.d)
        return apply_pointwise(lambda a:op(*a), cart, self.alphabet_func)

    def copy(self):
        ret = CantorPartition(self.alphabet_func, self.default)
        for v in self.d:
            ret.d[v] = self.d[v]
        return ret

# assume length at least 1
def cartesian_product(cps):
    #print("carting")
    if len(cps) == 0:
        #print("none")
        ret = CantorPartition(default = ())
        return ret
    elif len(cps) == 1:
        #print("one is", cps[0].d)
        ret = CantorPartition(alphabet_func = cps[0].alphabet_func)
        for v in cps[0].d:
            ret.d[(v,)] = cps[0].d[v]
        return ret
    else:
        #print("many case")
        af = cps[0].alphabet_func
        ret = CantorPartition(alphabet_func = af)
        cprod = cartesian_product(cps[1:])
        #print("cprod", cprod.d)
        # values are image tuples
        for u in cprod.d:
            for v in cps[0].d:
                #print(u, v)
                circ1 = cprod.d[u]
                circ2 = cps[0].d[v]
                # this circuit is the situation where we should
                # output (u,)+v
                circ3 = AND(circ1, circ2)
                if UNSAT_under(circ3, LDAC2(af)):
                    continue
                else:
                    ret.d[(v,) + u] = circ3
        return ret

def apply_pointwise(op, cp, alphabet_func):
    ret = CantorPartition(alphabet_func = alphabet_func)
    vals = set()
    for v in cp.d:
        #print("asmd", v, op(v))
        #if op(v) not in vals:
        #    ret.d[op(v)] = cp.d[v]
        #else:
        #    ret.d[op(v)] = OR(ret.d[op(v)], cp.d[v])
        ret[cp.d[v]] = op(v)
    return ret




"""
Example: \Z^2 with one node and alphabet {0, 1, 2}, explicit coding
i.e. also value 0 has a variable. CantorPartition is already aware
of the convention that our variable names are (..., val), and
such variable should have value 1 for exactly one val, and the possible
val's are given by an alphabet function.
"""
cp1 = CantorPartition(alphabet_func = lambda a:[0, 1, 2], default = 0)

cp1[V((0,0,0,0))] = 0
cp1[V((0,0,0,1))] = 1
cp1[V((0,0,0,2))] = 2

cp2 = CantorPartition(alphabet_func = lambda a:[0, 1, 2], default = 0)
cp2[V((1,0,0,0))] = 0
cp2[V((1,0,0,1))] = 1
cp2[V((1,0,0,2))] = 2

cp3 = cp1.apply((lambda a, b: (a - b) % 3), cp2)


