import diddy
from circuit import *

d = diddy.Diddy()

k = 3
n = 4

def dgeq(cxt, a, b, distbound):
    nodes, dim, topology, alphabet, formula, variables, aux_var, all_vars = cxt
    apos = variables[a]
    bpos = variables[b]
    # we explicitly list all pairs and make circuits manually
    alphabet = alphabet[0]
    circ = F
    for x in alphabet:
        for y in alphabet:
            if abs(x - y) >= distbound:
                #print(apos, x, bpos, y)
                circ = OR(circ, AND(V(apos + (x,)), V(bpos + (y,))))
    return circ

d.add_external("dgeq", dgeq)
d.run("""
%alphabet 0 1 2 3 4 5 6 7 -- n letters
%topology line
%SFT radio Ao Ap[o3]
  (o ~^1 p -> dgeq o p 3) &
  (o ~^2 p -> dgeq o p 2) &
  (o ~^3 p -> dgeq o p 1)
%SFT empty Ao 0=1
%equal radio empty
""")
#d.run("%tiler radio")





