# A super slow Game of Life implementation with explicit enumeration of cases.

import diddy
d = diddy.Diddy()
d.run("""
%topology king
%CA gol
0 1 Ao let threeE x := Ea[x1] Eb[x1] Ec[x1] a!@b!@c!@a & a=b=c=1 & Ad[x1] d = 1 -> ((d@a) | (d@b) | (d@c)) in
let fourE x := Ea[x1] Eb[x1] Ec[x1] Ed[x1] a!@b!@c!@d!@a!@c & b!@d & a=b=c=d=1 & Ae[x1] e = 1 -> (e@a | e@b | e@c | e@d) in
(o = 1 & fourE o) | threeE o
-- %spacetime_diagram golst gol
%SFT zero Ao o=0
%preimage zeropre gol zero
%tiler zeropre
""")


#d.run("""
#%topology king
#%CA xx
#0 1 Ao o@o
#%spacetime_diagram xx
#""")
