import circuit
from frozendict import frozendict as fd

class CircuitSet:
    def __init__(self):
        # from unique hashes to (circuit, int) pairs
        self.circuits = dict()
        #  patterns that separate circuits
        self.patterns = list()
        # running index
        self.count = 0
    def add(self, new, really_add = True):
        hashy = {}
        for p in self.patterns:
            hashy[p] = circuit.evaluate(new, p)
        hashy = fd(hashy)
        if hashy in self.circuits:
            (prev, ix) = self.circuits[hashy]
            m = circuit.equivalent(new, prev, True)
            if m == True:
                #self.existing = m
                return prev #False
            if really_add:
                self.add_pattern(fd(m))
                # now the hash has to be unique, so recursion is safe
                return self.add(new)
            else:
                return True
        else:
            if really_add:
                self.circuits[hashy] = (new, self.count)
                self.count += 1
                return new
            return True
    def add_pattern(self, pat):
        self.patterns.append(pat)
        newcircuits = {}
        for h in self.circuits:
            (circ, ix) = self.circuits[h]
            v = circuit.evaluate(circ, pat)
            hcopy = dict(h)
            hcopy[pat] = v
            newcircuits[fd(hcopy)] = (circ, ix)
        self.circuits = newcircuits
    def index(self, circ):
        # assumes circ is in the set
        hashy = {}
        for p in self.patterns:
            hashy[p] = evaluate(circ, p)
        return self.circuits[fd(hashy)][1]
    def __contains__(self, item):
        return not self.add(item, False)
    def __str__(self):
        return "CircuitSet container with %s circuits." % len(self.circuits)
    def __len__(self):
        return self.count
    def __iter__(self):
        return iter(c for (c,_) in self.circuits.values())

if __name__ == "__main__":
    s = CircuitSet()
    s.add(T)
    s.add(F)
    s.add(V("a"))
    s.add(V("b"))
    print(V("b") in s)
    print(AND(V("b"), V("a")) in s)
    print(AND(V("b"), V("b")) in s)
    print(OR(AND(V("b"), V("a")), NOT(V("b")), NOT(V("a"))) in s)
    print(OR(AND(V("b"), V("a")), NOT(V("b")), NOT(V("b"))) in s)
    print(s)
