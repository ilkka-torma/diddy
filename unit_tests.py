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
%containsF ver_golden_mean_shift hor_golden_mean_shift
%containsF golden_mean_shift hor_golden_mean_shift
%containsT ver_golden_mean_shift golden_mean_shift
%containsF ver_golden_mean_shift full_shift
%containsT full_shift hor_golden_mean_shift
%equalT hor_golden_mean_shift2 hor_golden_mean_shift
%equalT ver_golden_mean_shift ver_golden_mean_shift2
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
%show_formula hor_golden_mean_shift
%show_formula hor_golden_mean_shift2
%equalT hor_golden_mean_shift2 hor_golden_mean_shift
"""
unit_tests.append(("crazy gms", code_crazy_gms))

# golden mean shift on hexagon grid
code_hex_gms = """
%topology hex
%set gms Ao Ae[o1] o=0|e=0|o@e
%set gms2 Ao Ae[o5] o~~e -> (o=0| e = 0)
%set broken_gms Ao Ae[o1] o=0|e=0
%set broken_gms2 Ao Ae[o5] o~e -> (o=0| e = 0)
%set empty Ao 0=1
%set all_zero Ao o=0
%set fullshift Ao 0=0
%SFT byforbs
(0,0,0):1 (0,0,1):1;
(0,0,0):1 (-1,0,1):1;
(0,0,0):1 (0,1,1):1
-- %compare_SFT_pairs_equality
%equalT gms gms2
%equalF gms broken_gms2
%equalT all_zero broken_gms2
%equalT byforbs gms
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
%equalT idcode idcode2
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
xor (xor o=1 o.up=1) (xor o.dn=1 o.up.up=1)
%SFT test2 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor o=1 o.dn=1) o.up.up!=0) o.up=1
%SFT test3 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor o=1 o.dn.up=1) o.up.up!=0) o.up=1
%show_formula test2
-- %compare_SFT_pairs_equality
%equalT test test2
%equalF test test3
"""
unit_tests.append(("basic xors", code_basic_xors))

# ledrappier test
code_ledra = """
%topology grid
%SFT Ledrappier Ao let xor a b := (a & !b) | (!a & b) in
xor (xor o=1 o.up=1) o.rt=1
%SFT LedrappierSquare Ao let xor a b := (a & !b) | (!a & b) in
xor (xor o=1 o.up.up=1) o.rt.rt=1
--%compare_SFT_pairs
%containsF Ledrappier LedrappierSquare
%containsT LedrappierSquare Ledrappier
"""
unit_tests.append(("ledrappier", code_ledra))

code_trivial_WangTest = """
%nodes N E S W
%alphabet 0 1 2 3
%topology
up (0,0,N) (0,1,S)
dn (0,0,S) (0,-1,N)
rt (0,0,E) (1,0,W)
lt (0,0,W) (-1,0,E)
%SFT WangTest ACo
let WangConstraint o := o.N = o.up.S & o.E = o.rt.W in
WangConstraint o.rt.up &
o.N = o.up.S & o.E = o.rt.W &
o.N=0|o.N=1 &
o.S=0 &
o.W=0|o.W=1 &
o.E=0
%SFT WangTest2 Ao o=0
%show_formula WangTest2
%equalT WangTest WangTest2
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
0 1 Ao o!=o.rt;
%equalT a a
%compose_CA aa a a
%compose_CA aa_a aa a
%compose_CA a_aa a aa
%equalT a_aa aa_a
"""
unit_tests.append(("trivial CA associativity", code))

code = """
%CA a
0 1 Ao o!=o.rt;
%equalT a a
%compose_CA aa a a
%compose_CA aa_a aa a
%compose_CA a_aa a aa
%equalT a_aa aa_a
"""
unit_tests.append(("trivial CA associativity", code))



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
