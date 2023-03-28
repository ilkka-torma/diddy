import dparser
import compiler
import sft
import period_automaton
import time
import argparse
import fractions
import math

# just some basic checks
code_basic_comparisons = """
%nodes 0
%dim 2
%topology grid
%alphabet 0 1
%SFT full_shift              Ao 0 = 0
%SFT ver_golden_mean_shift  Ao o = 1 -> o.dn = 0
%SFT ver_golden_mean_shift2 Ao o.dn = 1 -> o = 0
%SFT hor_golden_mean_shift  Ao o = 1 -> o.rt = 0
%SFT golden_mean_shift      Ao o = 1 -> o.up = 0 & o.rt = 0
%SFT hor_golden_mean_shift2
(0,0,0):1 (1,0,0):1
%contains ver_golden_mean_shift hor_golden_mean_shift
%contains golden_mean_shift hor_golden_mean_shift
%contains ver_golden_mean_shift golden_mean_shift
%contains ver_golden_mean_shift full_shift
%contains full_shift hor_golden_mean_shift
%equal hor_golden_mean_shift2 hor_golden_mean_shift
%equal ver_golden_mean_shift ver_golden_mean_shift2
"""

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
%contains ver_golden_mean_shift hor_golden_mean_shift
%contains golden_mean_shift hor_golden_mean_shift
%contains ver_golden_mean_shift golden_mean_shift
%contains ver_golden_mean_shift full_shift
%contains full_shift hor_golden_mean_shift
%equal hor_golden_mean_shift2 hor_golden_mean_shift
%equal ver_golden_mean_shift ver_golden_mean_shift2
"""

# crazy golden mean shift formula / forbs
code_crazy_gms = """
%SFT hor_golden_mean_shift  Ao (o.rt.rt = 1 -> o.rt = 0) & Ae[o3] e.up = 0 | e.lt.up != e.rt.up.lt
%SFT hor_golden_mean_shift2
(0,0,0):1 (1,0,0):1 (0,3,0):0
(-1,1,0):1 (0,2,0):1 (0,3,0):1
(0,0,0):1 (1,0,0):1 (2,2,0):0
(0,0,0):1 (1,0,0):1 (2,2,0):1
%show_formula hor_golden_mean_shift
%show_formula hor_golden_mean_shift2
%equal hor_golden_mean_shift2 hor_golden_mean_shift
"""

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
(0,0,0):1 (0,0,1):1
(0,0,0):1 (-1,0,1):1
(0,0,0):1 (0,1,1):1
%compare_SFT_pairs_equality
"""


#_hex_idcodes = ""
code = """ 
%topology hex
%SFT idcode Ao let c u v := v = 1 & u ~ v in
(Ed[o1] c o d) & (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))
%SFT idcode2
(0,0,1):0 (0,0,0):0 (1,0,0):0 (0,-1,0):0
(0,0,1):0 (1,1,1):0 (2,0,0):0 (1,-1,0):0
(0,0,1):0 (1,1,0):0 (1,0,1):0 (2,1,0):0
(0,0,0):0 (0,0,1):0 (0,-1,0):0 (1,1,0):0 (1,1,1):0 (2,1,0):0
(0,0,0):0 (0,0,1):0 (1,0,0):0 (0,-1,1):0 (1,-1,0):0 (0,-2,0):0
(0,0,0):0 (0,0,1):0 (0,-1,0):0 (1,0,1):0 (2,0,0):0 (1,-1,0):0
(0,0,1):0 (1,0,0):0 (1,0,1):0 (1,1,1):0
(0,0,0):0 (0,-1,0):0 (1,0,1):0 (1,1,1):0
(0,0,1):0 (1,0,0):0 (1,1,1):0 (0,-1,1):0 (1,-1,0):0 (1,-1,1):0
(0,0,1):0 (1,0,0):0 (1,0,1):0 (2,1,0):0 (2,1,1):0 (2,2,1):0
(0,0,1):0 (1,0,0):0 (1,1,1):0 (2,0,0):0 (2,0,1):0 (2,1,1):0
--%compare_SFT_pairs
%calculate_forbidden_patterns idcode idcode3 3
%show_formula idcode2
%show_formula idcode3
"""

code_basic = """
%alphabet 0 1
%SFT fullshift      Ao 0=0
%SFT fullshift2      Ao o=o
%SFT not_fullshift  Ao o=0
-- %compare_SFT_pairs
%calculate_forbidden_patterns not_fullshift nf 2
"""

#testing one-dimensional XORs
code_basic_xors = """
%topology grid
%SFT test Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor o=1 o.up=1) (xor o.dn=1 o.up.up=1)
%SFT test2 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor o=1 o.dn=1) o.up.up!=0) o.up=1
%SFT test3 Ao Ap let xor a b := (a & !b) | (!a & b) in
xor (xor (xor o=1 o.dn.up=1) o.up.up!=0) o.up=1
%show_formula test2
%compare_SFT_pairs_equality
"""

# ledrappier test
code_ledra = """
%topology grid
%SFT Ledrappier Ao let xor a b := (a & !b) | (!a & b) in
xor (xor o=1 o.up=1) o.rt=1
%SFT LedrappierSquare Ao let xor a b := (a & !b) | (!a & b) in
xor (xor o=1 o.up.up=1) o.rt.rt=1
%compare_SFT_pairs
"""

#print(dparser.read_formula("Ao o!=1|o.rt!=1&o!=1|o.dn!=1"))
#a = bb

"""
(('NODEFORALL', 'o', None, ('AND', ('OR', ('NOT', ('HASVAL', 'o', 1)),
('NOT', ('HASVAL', ['o', 'rt'], 1))), ('OR', ('NOT', ('HASVAL', 'o', 1)),
('NOT', ('HASVAL', ['o', 'dn'], 1))))), '')
"""

# given list of tiles, return colors and formula
def Wang(tiles):
    ENWS_colors = set(), set(), set(), set()
    for t in tiles:
        for i in range(4):
            ENWS_colors[i].add(t[i])
    colors = ENWS_colors[0]
    colors = colors.union(ENWS_colors[1])
    colors = colors.union(ENWS_colors[2])
    colors = colors.union(ENWS_colors[3])
    formula = "ACo o.N = o.up.S & o.E = o.rt.W & (\n"
    if len(tiles) == 0:
        raise Exception("Empty list of Wang tiles not implemented.")
    for t in tiles:
        tile_formula = "("
        # (o.E=3 & o.N=1 & o.W=3 & o.S=3) |
        for d,i in zip("ENWS", t):
            # i[1] is already parsed but is rewritten to formula...
            tile_formula += "o.%s=%s & " % (d, str(i))
        formula += tile_formula[:-3] + ") |\n"
    formula = formula[:-3] + ")"
    #print(formula)
    return list(colors), dparser.read_formula(formula)[0]

# given fof (formula or forbos), convert to a (parsed) formula
def forbos_to_formula(fof):
    #print("gille", fof)
    #if fof[0] == "formula":
    #    return fof[1]
    #assert fof[0] == "forbos"
    #fof = fof[1]
    preamble = ("CELLFORALL", "o", None)
    #print (fof)
    andeds = []
    # f goes over 
    for f in fof:
        # print(f, "limas",)
        oreds = []
        for vec in f:
            oreds.append(("NOT", ("HASVAL", ["o", vec], f[vec])))
        andeds.append(("OR",) + tuple(oreds))
    ret = preamble + (("AND",) + tuple(andeds),)
    #print(ret, "MIL")
    return ret
        
def report_SFT_contains(a, b, mode="report", truth=True):
    aname, aSFT = a
    bname, bSFT = b
    print("Testing whether %s contains %s." % (aname, bname))
    tim = time.time()
    res, rad = aSFT.contains(bSFT, return_radius = True)
    tim = time.time() - tim
    if res:
        print("%s CONTAINS %s (radius %s, time %s)" % (aname, bname, rad, tim))
    else:
        print("%s DOES NOT CONTAIN %s (radius %s, time %s)" % (aname, bname, rad, tim))
    print()
    if mode == "assert":
        print(res, truth)
        assert res == (truth == "T")

def report_SFT_equal(a, b, mode="report", truth=True):
    aname, aSFT = a
    bname, bSFT = b
    print("Testing whether %s and %s are equal." % (aname, bname))
    tim = time.time()
    res, rad = aSFT.equals(bSFT, return_radius = True)
    tim = time.time() - tim
    if res: 
        print("They are EQUAL (radius %s, time %s)." % (rad, tim))
    else:
        print("They are DIFFERENT (radius %s, time %s)." % (rad, tim))
    print()
    if mode == "assert":
        print(res, truth)
        assert res == (truth == "T")

grid = [("up", (0,0,0), (0,1,0)),
        ("dn", (0,0,0), (0,-1,0)),
        ("rt", (0,0,0), (1,0,0)),
        ("lt", (0,0,0), (-1,0,0))]
hexgrid = [("up", (0,0,0), (0,1,1)),
           ("dn", (0,0,1), (0,-1,0)),
           ("rt", (0,0,0), (0,0,1)),
           ("lt", (0,0,0), (-1,0,1)),
           ("rt", (0,0,1), (1,0,0)),
           ("lt", (0,0,1), (0,0,0))]
kinggrid = [("E", (0,0,0), (1,0,0)),
            ("NE", (0,0,0), (1,1,0)),
            ("N", (0,0,0), (0,1,0)),
            ("NW", (0,0,0), (-1,1,0)),
            ("W", (0,0,0), (-1,0,0)),
            ("SW", (0,0,0), (-1,-1,0)),
            ("S", (0,0,0), (0,-1,0)),
            ("SE", (0,0,0), (1,-1,0))]
trianglegrid = [("E", (0,0,0), (1,0,0)),
            ("NE", (0,0,0), (1,1,0)),
            ("N", (0,0,0), (0,1,0)),
            ("W", (0,0,0), (-1,0,0)),
            ("SW", (0,0,0), (-1,-1,0)),
            ("S", (0,0,0), (0,-1,0))]

Wang_nodes = ["E", "N", "W", "S"]
Wang_topology = [("up", (0,0,"N"), (0,1,"S")),
                 ("dn", (0,0,"S"), (0,-1,"N")),
                 ("rt", (0,0,"E"), (1,0,"W")),
                 ("lt", (0,0,"W"), (-1,0,"E"))]

def run_diddy(code, mode="report"):
    print(code)
    parsed = dparser.parse(code)
    nodes = [0]
    alphabet = [0, 1]
    dim = 2
    topology = grid
    SFTs = {}
    clopens = {}
    formulae = []
    for i in parsed:
        if i[0] == "nodes":
            nodes = i[1]
        elif i[0] == "dim":
            dim = i[1]        
        elif i[0] == "alphabet":
            alphabet = i[1]
        elif i[0] == "topology":
            if i[1] in ["square", "grid", "squaregrid"]:
                topology = grid
                nodes = [0]
            elif i[1] in ["hex", "hexgrid"]:
                topology = hexgrid
                nodes = [0, 1]
            elif i[1] in ["king", "kinggrid"]:
                topology = kinggrid
                nodes = [0]
            elif i[1] in ["triangle", "trianglegrid"]:
                topology = trianglegrid
                nodes = [0]
            else:
                topology = i[1]
            #print(topology)
                
        elif i[0] == "SFT":
            #print(i)
            if i[2] == "formula":
                #print (i[3])
                circ = compiler.formula_to_circuit(nodes, dim, topology, alphabet, i[3])
                SFTs[i[1]] = sft.SFT(dim, nodes, alphabet, circuit=circ, formula=i[3])
                #print(formula)
            elif i[2] == "forbos":
                #print(i[3])
                SFTs[i[1]] = sft.SFT(dim, nodes, alphabet, forbs=i[3])
            else:
                raise Exception("??")

        elif i[0] == "clopen":
            compiled = compiler.formula_to_circuit(nodes, dim, topology, alphabet, i[2])
            clopens[i[1]] = i[2]
            
        elif i[0] == "minimum_density":
            verbose_here = False
            if i[1] not in SFTs:
                raise Exception("Density can only be calculated for SFTs, not %s." % i[1])
            tim = time.time()
            the_sft = SFTs[i[1]]
            periods = i[2]
            print("Computing minimum density for %s restricted to period(s) %s"%(i[1], periods))
            nfa = period_automaton.PeriodAutomaton(the_sft, periods)
            if verbose_here: print("const")
            nfa.populate()
            if verbose_here: print("popula")
            nfa.minimize()
            comps = list(nfa.strong_components())
            if verbose_here: print("strng com")
            del nfa
            min_data = (math.inf,)
            min_comp = None
            for (ic, comp) in enumerate(comps):
                data = comp.linsqrt_min_density_cycle()
                if data[:1] < min_data[:1]:
                    min_data = data
                    min_aut = comp
            if verbose_here: print("kikek")
            dens, minlen, stcyc, cyc = min_data
            border_size = len(the_sft.nodes)*len(min_aut.frontier)
            print("Density", fractions.Fraction(sum(b for fr in cyc for b in fr.values()),
                                                len(cyc)*border_size), "~", dens/border_size, "realized by cycle of length", len(cyc))
            print([(period_automaton.nvadd(nvec,(tr,)+(0,)*(dim-1)),c) for (tr,pat) in enumerate(cyc) for (nvec,c) in sorted(pat.items())])
            print("Calculation took", time.time() - tim, "seconds.") 

        elif i[0] == "show_formula" and mode == "report":
            if i[1] in SFTs:
                formula = SFTs[i[1]].circuit
            elif i[1] in clopens:
                formula = clopens[i[1]][2]
            else:
                raise Exception("No set named %s" % i[1])
            print("Showing compiled formula for %s." % i[1])
            print(formula)
            print()
            
        elif i[0] == "show_parsed" and mode == "report":
            if i[1] in SFTs:
                formula = SFTs[i[1]].formula
            elif i[1] in clopens:
                formula = clopens[i[1]][2]
            else:
                raise Exception("No set named %s" % i[1])
            print("Showing parsed formula for %s." % i[1])
            print(formula)
            print()

        elif i[0][:5] == "equal":
            if i[1] in SFTs and i[2] in SFTs:
                SFT1 = SFTs[i[1]]
                SFT2 = SFTs[i[2]]
                report_SFT_equal((i[1], SFT1), (i[2], SFT2), mode=mode, truth=i[0][5:])

            else:
                raise Exception("%s or %s is not an SFT." % i[1:])
            
                #if i[1] not in clopens or i[2] not in clopens:
                #    raise Exception("%s not a clopen set"i[1] )                
                #clopen1 = clopens[i[1]]
                #clopen2 = clopens[i[2]]
                #raise Exception("Comparison of clopen sets not implemented.")
                
        elif i[0][:8] == "contains":

            if i[1] in SFTs:
                SFT1 = SFTs[i[1]]
                SFT2 = SFTs[i[2]]
                report_SFT_contains((i[1], SFT1), (i[2], SFT2), mode=mode, truth=i[0][8:])
            else:
                clopen1 = clopens[i[1]]
                clopen2 = clopens[i[2]]
                raise Exception("Comparison of clopen sets not implemented.")

        elif i[0] == "compare_SFT_pairs" and mode == "report":
            for a in SFTs:
                for b in SFTs:
                    if a == b:
                        continue
                    report_SFT_contains((a, SFTs[a]), (b, SFTs[b]))

        elif i[0] == "compare_SFT_pairs_equality" and mode == "report":
            #print(SFTs_as_list)
            for (i, (aname, a)) in enumerate(SFTs.items()):# SFTs_as_list):
                for (bname, b) in list(SFTs.items())[i+1:]: #SFTs_as_list[i+1:]:
                    report_SFT_equal((aname, a), (bname, b))

        elif i[0] == "show_forbidden_patterns":
            
            the_sft = SFTs[i[1]]
            print("Showing forbidden patterns for %s." % i[1])
            if the_sft.forbs is None:
                print("Forbidden patterns not yet computed.")
            else:
                print(the_sft.forbs)
            print()

        elif i[0] == "compute_forbidden_patterns":
            
            the_sft = SFTs[i[1]]
            rad = i[2]
            if mode == "report":
                print("Computing forbidden patterns for %s using radius %s." % (i[1], rad))
                if the_sft.forbs is not None:
                    print("It already had forbidden patterns; overwriting them.")
                print()
            the_sft.deduce_forbs(rad)

        elif i[0] == "set_weights":
            print (i[1])

        elif i[0] == "Wang" or i[0] == "wang":
            name = i[1]
            print(i[1])
            tiles = i[2]
            # for now, Wang tiles are always two-dimensional
            colors, formula = Wang(tiles)
            # print(formula)
            circ = compiler.formula_to_circuit(Wang_nodes, 2, Wang_topology, colors, formula)
            SFTs[name] = sft.SFT(2, Wang_nodes, alphabet, circuit=circ, formula=formula)

        elif mode == "report":
            raise Exception("Unknown command %s." % i[0])


if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("filename", metavar='f', type=str)
    args = arg_parser.parse_args()

    with open(args.filename, 'r') as f:
        code = f.read()

    run_diddy(code)
