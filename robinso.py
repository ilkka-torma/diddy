import diddy
d = diddy.Diddy()

d.run("""
-- Robinson tiling
%nodes H V N E S W
%alphabet default=[U L R i l r] {H : [0 1] V : [0 1]}
%SFT robinson ACo
let cross n e s w :=
  (n = L & e = R & s = U & w = U)
in
let rob n e s w :=
  cross n e s w |
  (n = i & e = i & s = U & w = i) |
  (n = l & e = i & s = R & w = i) |
  (n = r & e = i & s = L & w = i) |
  (n = i & e = r & s = U & w = l) |
  (n = l & e = r & s = R & w = l) |
  (n = r & e = r & s = L & w = l)
in
let invers a b :=
 (a = U <-> b = i) &
 (a = L <-> b = r) &
 (a = R <-> b = l)
in
let inverse a b :=
 invers a b &
 invers b a
in
  (rob o.N o.E o.S o.W |
   rob o.E o.S o.W o.N |
   rob o.S o.W o.N o.E |
   rob o.W o.N o.E o.S)
   &
  -- update parity
  o.H = o.(0,1).H &
  o.H != o.(1,0).H &
  o.V = o.(1,0).V &
  o.V != o.(0,1).V &
  -- check crosses at even positions
  (o.H = o.V = 1 ->
  (cross o.N o.E o.S o.W |
   cross o.E o.S o.W o.N |
   cross o.S o.W o.N o.E |
   cross o.W o.N o.E o.S)) &
 inverse o.E o.(1,0).W &
 inverse o.N o.(0,1).S
%tiler x_size=20 y_size=20
  node_offsets={H:[2/5 2/5] V:[3/5 3/5] N:[1/2 4/5] E:[4/5 1/2] S:[1/2 1/5] W:[1/5 1/2]}
  robinson
""")


