import diddy
d = diddy.Diddy()

# Robinson tiles and Jarkko's exercise HW7 ex5

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
  -- for Jarkko's exercise, drop this line
  (o.H = o.V = 1 -> (cross o.N o.E o.S o.W | cross o.E o.S o.W o.N | cross o.S o.W o.N o.E | cross o.W o.N o.E o.S)) &

 inverse o.E o.(1,0).W &
 inverse o.N o.(0,1).S

--%tiler x_size=1 y_size=1
--  node_offsets={H:[3/7 3/7] V:[4/7 4/7] N:[1/2 4/5] E:[4/5 1/2] S:[1/2 1/5] W:[1/5 1/2]}
--  pictures={E:[robU robUL robUR robU_r180 robUR_r180 robUL_r180]
--            N:[robU_r90 robUL_r90 robUR_r90 robU_r270 robUR_r270 robUL_r270]
--            W:[robU_r180 robUL_r180 robUR_r180 robU robUR robUL]
--            S:[robU_r270 robUL_r270 robUR_r270 robU_r90 robUR_r90 robUL_r90]}
--  robinson

%tiler x_size=12 y_size=12 -- @x_periodic @y_periodic
  node_offsets={H:[3/7 3/7] V:[4/7 4/7] N:[1/2 4/5] E:[4/5 1/2] S:[1/2 1/5] W:[1/5 1/2]}
  pictures={E:[robU robUL robUR robU_r180 robUR_r180 robUL_r180]
            N:[robU_r90 robUL_r90 robUR_r90 robU_r270 robUR_r270 robUL_r270]
            W:[robU_r180 robUL_r180 robUR_r180 robU robUR robUL]
            S:[robU_r270 robUL_r270 robUR_r270 robU_r90 robUR_r90 robUL_r90]}
  robinson
""")


