import diddy
import time

unit_tests = []

# whether we test the ones that take like 10 seconds
long_ones_too = False

# just some basic checks
code_basic_comparisons = """
%nodes 0
%dim 2
%topology grid
%alphabet 0 1
%SFT full_shift             Ao 0 = 0
%SFT ver_golden_mean_shift  Ao o = 1 -> o.dn = 0
%SFT ver_golden_mean_shift2 Ao o.dn = 1 -> o = 0
%SFT hor_golden_mean_shift  Ao o = 1 -> o.rt = 0
%SFT golden_mean_shift      Ao o = 1 -> o.up = 0 & o.rt = 0
%SFT hor_golden_mean_shift2
(0,0,0):1 (1,0,0):1
%contains expect=F ver_golden_mean_shift hor_golden_mean_shift
%contains expect=F golden_mean_shift hor_golden_mean_shift
%contains expect=T ver_golden_mean_shift golden_mean_shift
%contains expect=F ver_golden_mean_shift full_shift
%contains expect=T full_shift hor_golden_mean_shift
%equal expect=T hor_golden_mean_shift2 hor_golden_mean_shift
%equal expect=T ver_golden_mean_shift ver_golden_mean_shift2
"""
unit_tests.append(("basic comparisons", code_basic_comparisons))

# crazy golden mean shift formula / forbs
code_crazy_gms = """
%SFT hor_golden_mean_shift  Ao (o.rt.rt = 1 -> o.rt = 0) & Ae[o3] e.up = 0 | e.lt.up != e.rt.up.lt
%SFT hor_golden_mean_shift2
(0,0,0):1 (1,0,0):1 (0,3,0):0;
(0,0,0):1 (1,0,0):1 (0,3,0):1;
(0,0,0):1 (1,0,0):1 (2,2,0):0;
(0,0,0):1 (1,0,0):1 (2,2,0):1
%SFT hor_golden_mean_shift3 Ao (o.(2,0) = 1 -> o.(1,0) = 0) & Ae[o3] e.(0,1) = 0 | e.(-1,1) != e.(0,1)
%show_formula hor_golden_mean_shift
%show_formula hor_golden_mean_shift2
%show_formula hor_golden_mean_shift3
%equal expect=T hor_golden_mean_shift2 hor_golden_mean_shift
%equal expect=T hor_golden_mean_shift3 hor_golden_mean_shift
"""
unit_tests.append(("crazy gms", code_crazy_gms))

# golden mean shift on hexagon grid
code_hex_gms = """
%topology hex
%SFT gms Ao Ae[o1] o=0|e=0|o@e
%SFT gms2 Ao Ae[o5] o~~e -> (o=0| e = 0)
%SFT broken_gms Ao Ae[o1] o=0|e=0
%SFT broken_gms2 Ao Ae[o5] o~e -> (o=0| e = 0)
%SFT empty Ao 0=1
%SFT all_zero Ao o=0
%SFT fullshift Ao 0=0
%SFT byforbs
(0,0,0):1 (0,0,1):1;
(0,0,0):1 (-1,0,1):1;
(0,0,0):1 (0,1,1):1
-- %compare_SFT_pairs_equality
%equal expect=T gms gms2
%equal expect=F gms broken_gms2
%equal expect=T all_zero broken_gms2
%equal expect=T byforbs gms
"""
unit_tests.append(("hex gms", code_hex_gms))

# = ""
code_hex_idcodes = """ 
%topology hex
%SFT idcode Ao let c u v := v = 1 & u ~ v in
(Ed[o1] c o d) & (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))
%SFT idcode2
(0,0,1):0 (0,0,0):0 (1,0,0):0 (0,-1,0):0;
(0,0,1):0 (1,1,1):0 (2,0,0):0 (1,-1,0):0;
(0,0,1):0 (1,1,0):0 (1,0,1):0 (2,1,0):0;
(0,0,0):0 (0,0,1):0 (0,-1,0):0 (1,1,0):0 (1,1,1):0 (2,1,0):0;
(0,0,0):0 (0,0,1):0 (1,0,0):0 (0,-1,1):0 (1,-1,0):0 (0,-2,0):0;
(0,0,0):0 (0,0,1):0 (0,-1,0):0 (1,0,1):0 (2,0,0):0 (1,-1,0):0;
(0,0,1):0 (1,0,0):0 (1,0,1):0 (1,1,1):0;
(0,0,0):0 (0,-1,0):0 (1,0,1):0 (1,1,1):0;
(0,0,1):0 (1,0,0):0 (1,1,1):0 (0,-1,1):0 (1,-1,0):0 (1,-1,1):0;
(0,0,1):0 (1,0,0):0 (1,0,1):0 (2,1,0):0 (2,1,1):0 (2,2,1):0;
(0,0,1):0 (1,0,0):0 (1,1,1):0 (2,0,0):0 (2,0,1):0 (2,1,1):0
-- %compare_SFT_pairs
--%calculate_forbidden_patterns idcode idcode3 3
--%show_formula idcode2
--%show_formula idcode3
%equal expect=T idcode idcode2
"""
unit_tests.append(("hex idcodes", code_hex_idcodes))

code_basic = """
%alphabet 0 1
%SFT fullshift      Ao 0=0
%SFT fullshift2      Ao o=o
%SFT not_fullshift  Ao o=0
-- %compare_SFT_pairs
%calculate_forbidden_patterns not_fullshift nf 2
"""
# unit_tests.append(code_basic)

#testing one-dimensional XORs; first two are equal
code_basic_xors = """
%topology grid
%SFT test Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up=1)) (xor (o.dn=1) (o.up.up=1))
%SFT test2 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor (o=1) (o.dn=1)) (o.up.up!=0)) (o.up=1)
%SFT test3 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor (o=1) (o.dn.up=1)) (o.up.up!=0)) (o.up=1)
%show_formula test2
-- %compare_SFT_pairs_equality
%equal expect=T test test2
%equal expect=F test test3
"""
unit_tests.append(("basic xors", code_basic_xors))

# ledrappier test
code_ledra = """
%topology grid
%SFT Ledrappier Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up=1)) (o.rt=1)
%SFT LedrappierSquare Ao let xor a b := (a & !b) | (!a & b) in
xor (xor (o=1) (o.up.up=1)) (o.rt.rt=1)
--%compare_SFT_pairs
%contains expect=F Ledrappier LedrappierSquare
%contains expect=T LedrappierSquare Ledrappier
"""
unit_tests.append(("ledrappier", code_ledra))

code_trivial_WangTest = """
%nodes N E S W
%alphabet 0 1 2 3
%topology
up (0,0,N) (0,1,S);
dn (0,0,S) (0,-1,N);
rt (0,0,E) (1,0,W);
lt (0,0,W) (-1,0,E);
%SFT WangTest ACo
let WangConstraint o := o.N = o.up.S & o.E = o.rt.W in
WangConstraint o.rt.up &
o.N = o.up.S & o.E = o.rt.W &
(o.N=0|o.N=1) &
o.S=0 &
(o.W=0|o.W=1) &
o.E=0
%SFT WangTest2 Ao o=0
%show_formula WangTest2
%equal expect=T WangTest WangTest2
"""
unit_tests.append(("trivial Wang test", code_trivial_WangTest))

# jeandel-rao
code_JR = """
%nodes N E S W
%alphabet 0 1 2 3 4
%topology
up (0,0,N) (0,1,S)
dn (0,0,S) (0,-1,N)
rt (0,0,E) (1,0,W)
lt (0,0,W) (-1,0,E)
%SFT JeandelRao ACo
let WangConstraint o := o.N = o.up.S & o.E = o.rt.W in
WangConstraint o &
-- 1131
(o.E=1 & o.N=1 & o.W=3 & o.S=1) |
-- 1232
(o.E=1 & o.N=2 & o.W=3 & o.S=2) |
-- 3133
(o.E=3 & o.N=1 & o.W=3 & o.S=3) |
-- 2421
(o.E=2 & o.N=4 & o.W=2 & o.S=1) |
-- 2220
(o.E=2 & o.N=2 & o.W=2 & o.S=0) |
-- 0001
(o.E=0 & o.N=0 & o.W=0 & o.S=1) |
-- 3102
(o.E=3 & o.N=1 & o.W=0 & o.S=2) |
-- 0212
(o.E=0 & o.N=2 & o.W=1 & o.S=2) |
-- 1214
(o.E=1 & o.N=2 & o.W=1 & o.S=4) |
-- 3312
(o.E=3 & o.N=3 & o.W=1 & o.S=2) |
-- 0131
(o.E=0 & o.N=1 & o.W=3 & o.S=1)
%SFT empty Ao 0=1
%contains empty JeandelRao
"""

code_locdomrad2 = """
-- using a cache multiplies time usage by up to 5
-- but drops memory usage to fraction
--%start_cache 10 60 
%topology grid

%SFT locdomrad22 Ao
o=0 -> (Ep[o2] p=1) &
       (Ap[o1] p=0 -> (Eq[o2] q=1 & !Er[p1] r~q) |
                      (Eq[p2] q=1 & !Er[o1] r~q))

%SFT locdomrad24 Ao
o=0 -> (Ep[o2] p=1) &
       (Ap[o4] p=0 -> (Eq[o2] q=1 & Ar[p2] r!@q) |
                      (Eq[p2] q=1 & Ar[o2] r!@q))


%SFT locdomrad2x Ao let c a b := b=1 & Ed[a1] d~b in
o=0 -> (Et[o2] c o t) &
       (Ap[o4] p=0 -> Eq[o2p2] (c o q & !c p q) | (!c o q & c p q))

-- %compare_SFT_pairs
%equalT locdomrad22 locdomrad24
%equalT locdomrad22 locdomrad2x
--%end_cache
"""
if long_ones_too:
    unit_tests.append(("loc dom rad 2", code_locdomrad2))

code = """
%CA a
0 1 Ao o!=o.rt
%equal expect=T a a
%compose aa a a
%compose aa_a aa a
%compose a_aa a aa
%equal expect=T a_aa aa_a
"""
unit_tests.append(("trivial CA associativity", code))

code = """
%alphabet a b
%SFT goldenmean Ao o=a -> o.rt=b & o.up=b
%compute_forbidden_patterns radius=2 goldenmean
%set_weights a:0 b:2
%minimum_density expect=2 goldenmean (0,1)
%minimum_density expect=1 goldenmean (0,2)
%minimum_density expect=6/5 goldenmean (2,3)
"""
unit_tests.append(("golden mean upper density", code))

code = """
%alphabet a b
%SFT goldenmean Ao o=a -> o.rt=b & o.up=b
%set_weights a:0 b:2
%density_lower_bound expect=1 goldenmean (0,0,0) (1,0,0) (-1,0,0) (0,1,0) (0,-1,0); (0,1) (1,0)
"""
unit_tests.append(("golden mean lower density", code))

code = """
%SFT quarter Ao o=1 -> o.up=1 & o.rt=1
%SFT half Ao (o=o.lt=o.rt & (o=1 -> o.up=1)) | (o=o.up=o.dn & (o=1 -> o.rt=1))
%SFT two Ao o=o.up=o.rt
%contains expect=T quarter half
%contains expect=T half two
%contains expect=F method=recognizable two half
%contains expect=F method=recognizable two quarter
%contains expect=F method=recognizable half quarter
"""
unit_tests.append(("recog comparison", code))

code = """
%SFT onezero Ao (o=0 -> o.up=0) & (o=1 -> o.dn.dn=0)
%SFT zero Ao o=0
%equal expect=T onezero zero
%SFT onezero1 onesided=[1] Ao (o=0 -> o.up=0) & (o=1 -> o.dn.dn=0)
%SFT zero1 onesided=[1] Ao o=0
%contains expect=T onezero1 zero1
%contains expect=F zero1 onezero1
"""
unit_tests.append(("onesided comparison", code))

code = """
%dim 1
%nodes 0
%topology succ (0,0) (1,0)
%CA xor
0 1 Ao o!=o.succ
%spacetime_diagram diagram xor
%dim 2
%topology grid
%SFT var onesided=[1] Ao o!=o.rt <-> o.up=1
%equal expect=T diagram var
"""
unit_tests.append(("spacetime diagram", code))

code = """
%alphabet 0 1 2
%SFT long_dist Ao o=1 -> Ep[o4] p=2 & o ~^1,3 p
%SFT long_dist2 Ao o=1 ->
o.(3,0)=2 | o.(2,1)=2 | o.(1,2)=2 | o.(0,3)=2 |
o.(-1,2)=2 | o.(-2,1)=2 | o.(-3,0)=2 |
o.(-2,-1)=2 | o.(-1,-2)=2 | o.(0,-3)=2 |
o.(1,-2)=2 | o.(2,-1)=2 |
o.(0,1)=2 | o.(1,0)=2 | o.(0,-1)=2 | o.(-1,0)=2
%equal expect=T long_dist long_dist2
"""
unit_tests.append(("distance", code))

code = """
%nodes {t1 : [a] t2 : {t21:[0 1] t22:[a b]}}
%topology
e1 (0,0,t1.a) (0,0,t2.t21.0);
e2 (0,0,t1.a) (0,0,t2.t21.1);
e3 (0,0,t1.a) (0,0,t2.t22.a);
e4 (0,0,t1.a) (0,0,t2.t22.b);
e5 (0,0,t2.t21.0) (0,0,t1.a);
e6 (0,0,t2.t21.1) (0,0,t1.a);
e7 (0,0,t2.t22.a) (0,0,t1.a);
e8 (0,0,t2.t22.b) (0,0,t1.a)
%SFT a0 Ao o._.t1.a=0 <-> o=0
%SFT a1 Ao Ax[o1] o=x
%SFT a2
(0,0,t1.a):0 (0,0,t2.t21.0):1;
(0,0,t1.a):0 (0,0,t2.t21.1):1;
(0,0,t1.a):0 (0,0,t2.t22.a):1;
(0,0,t1.a):0 (0,0,t2.t22.b):1;
(0,0,t1.a):1 (0,0,t2.t21.0):0;
(0,0,t1.a):1 (0,0,t2.t21.1):0;
(0,0,t1.a):1 (0,0,t2.t22.a):0;
(0,0,t1.a):1 (0,0,t2.t22.b):0
%equal expect=T a0 a1
%equal expect=T a0 a2
"""
unit_tests.append(("tracks", code))

code = """
%nodes 0 1 2 3
%alphabet default=[0 1] {2 : [2 X] 3 : [1 2]}
%SFT test ACo o.0!=1 -> (o.up.1=1 & o.3=2 & o.rt.0=1) | o.2=X
%compute_forbidden_patterns test
%set_weights 0:1 1:3 2:2 X:4
%minimum_density test (0,3)
"""
unit_tests.append(("node-specific alphabets", code))

code = """
%sft empty Ao 0=1
%sft empty2 Ao 1=0
%sft nonempty Ao o=0
%sft nontriv_empty Ao
(o=0 -> o.rt=0 & o.up=1) &
(o=1 -> o.rt.rt=0)
%equal expect=F empty nonempty
%equal expect=T empty empty2
%equal expect=T empty nontriv_empty
"""
unit_tests.append(("emptiness", code))

code = """
%CA a
0 0 Ao o=o.rt=0
%CA b
0 0 Ao o=o.up=0
%calculate_CA_ball 3 a b
"""
unit_tests.append(("CA ball", code))

code = """
%nodes a b
%topology
sw (0,0,a) (0,0,b);
sw (0,0,b) (0,0,a)
%alphabet X Y
%save_environment env
%topology grid
%alphabet 0 1
%block_map domain=env b1
0 0 Ao o=o.sw
%block_map domain=env b2
0 0 ACo o.a=o.b
%equal expect=T b1 b2
"""
unit_tests.append(("environments and block maps", code))

code = """
%CA f
0 0 Ao o=o.up=0
%SFT domino Ao o!=o.rt
%preimage preim f domino
%SFT alternative Ao o=o.up=0 <-> (o.rt=1 | o.rt.up=1)
%equal expect=T preim alternative
"""
unit_tests.append(("preimage", code))

code = """
%SFT test Ao [o o.rt o.up] != [0 0 0]
%SFT test2 Ao o=1 | o.rt=1 | o.up=1
%SFT test3 Ao [o o.rt o.up] = [0 1 1] | o=1
%SFT test4 Ao o=0 -> o.rt=o.up!=0
%equal expect=T test test2
%equal expect=F test2 test3
%equal expect=T test3 test4
"""
unit_tests.append(("node lists", code))

code = """
%CA xor
0 0 Ao o=o.up=o.rt=0 | o=o.up!=o.rt=0 | 0=o!=o.up=o.rt | o=o.rt!=o.up=0
%fixed_points fps xor
%SFT diag Ao o.up=o.rt
%equal expect=T fps diag
"""
unit_tests.append(("fixed points", code))

code = """
%SFT a1 Ao o=o.rt
%SFT a2 Ao o=o.up
%intersection a3 a1 a2
%SFT b1 Ao o=o.rt=o.up
%equal expect=T a3 b1
%product tracks=[a b] a4 a1 a2
%nodes {a:[0] b:[0]}
%SFT b2 ACo o.a.0=o.(1,0).a.0 & o.b.0=o.(0,1).b.0
%equal expect=T a4 b2
"""
unit_tests.append(("intersection and product", code))

code = """
%save_environment bin
%alphabet a b c
%block_map codomain=bin f
0 1 Ao o=o.rt=a | o=o.up=b
%relation tracks=[D C] rel f
%nodes {D:[0] C:[0]}
%alphabet {D:[a b c] C:[0 1]}
%SFT a ACo o.C.0=1 <-> (o.D.0=o.(1,0).D.0=a | o.D.0=o.(0,1).D.0=b)
%equal expect=T rel a
"""
unit_tests.append(("relation", code))


if __name__ == "__main__":

    t = time.time()

    import os
    import psutil
    process = psutil.Process(os.getpid())
    start_mem = process.memory_info().rss/1000

    for (name, code) in unit_tests:
        diddy_inst = diddy.Diddy()
        print("Running test", name)
        diddy_inst.run(code, "assert")
#print("total time", time.time()-t)
    
    total_time = time.time() - t
    end_mem = process.memory_info().rss/1000

    print("time", total_time, "memory", start_mem, "->", end_mem)
