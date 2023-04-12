import dparser

import compiler
import sft

import period_automaton
import time

import argparse
import fractions
import math


import blockmap


class Diddy:
    def __init__(self):
        self.SFTs = {}
        self.CAs = {}
        self.clopens = {}
        self.nodes = [0]
        self.alphabet = [0, 1]
        self.dim = 2
        self.topology = grid
        self.formulae = []
        self.weights = None

    def run(self, code, mode="report"):
        #print(code)
        #import sys
        #sys.stdout = "messias"
        parsed = dparser.parse(code)
        for i in parsed:
            if i[0] == "nodes":
                self.nodes = i[1]
            elif i[0] == "dim":
                self.dim = i[1]        
            elif i[0] == "alphabet":
                self.alphabet = i[1]
            elif i[0] == "topology":
                if i[1] in ["square", "grid", "squaregrid"]:
                    self.topology = grid
                    self.nodes = [0]
                elif i[1] in ["hex", "hexgrid"]:
                    self.topology = hexgrid
                    self.nodes = [0, 1]
                elif i[1] in ["king", "kinggrid"]:
                    self.topology = kinggrid
                    self.nodes = [0]
                elif i[1] in ["triangle", "trianglegrid"]:
                    self.topology = trianglegrid
                    self.nodes = [0]
                else:
                    self.topology = i[1]
                #print(topology)
                    
            elif i[0] == "SFT":
                #print(i)
                if i[2] == "formula":
                    #print (i[3])
                    circ = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet, i[3])
                    self.SFTs[i[1]] = sft.SFT(self.dim, self.nodes, self.alphabet, circuit=circ, formula=i[3])
                    #print(formula)
                elif i[2] == "forbos":
                    #print(i[3])
                    self.SFTs[i[1]] = sft.SFT(self.dim, self.nodes, self.alphabet, forbs=i[3])
                else:
                    raise Exception("??")

            elif i[0] == "clopen":
                compiled = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet, i[2])
                self.clopens[i[1]] = i[2]
                
            elif i[0] == "minimum_density":
                verbose_here = False
                if i[1] not in self.SFTs:
                    raise Exception("Density can only be calculated for SFTs, not %s." % i[1])
                tim = time.time()
                the_sft = self.SFTs[i[1]]
                periods = i[2]
                print("Computing minimum density for %s restricted to period(s) %s"%(i[1], periods) + " using weights {}".format(self.weights) if self.weights is not None else "")
                nfa = period_automaton.PeriodAutomaton(the_sft, periods, weights=self.weights)
                if verbose_here: print("const")
                nfa.populate()
                if verbose_here: print("popula")
                nfa.minimize()
                comps = list(nfa.strong_components())
                if verbose_here: print("strng com")
                del nfa
                min_data = (math.inf,)
                min_aut = None
                for (ic, comp) in enumerate(comps):
                    data = comp.linsqrt_min_density_cycle()
                    if data[:1] < min_data[:1]:
                        min_data = data
                        min_aut = comp
                if verbose_here: print("kikek")
                dens, minlen, stcyc, cyc = min_data
                border_size = len(the_sft.nodes)*len(min_aut.frontier)
                print("Density", fractions.Fraction(sum(weights[b] for fr in cyc for b in fr.values()),
                                                    len(cyc)*border_size), "~", dens/(border_size*min_aut.weight_denominator), "realized by cycle of length", len(cyc))
                print([(period_automaton.nvadd(nvec,(tr,)+(0,)*(dim-1)),c) for (tr,pat) in enumerate(cyc) for (nvec,c) in sorted(pat.items())])
                print("Calculation took", time.time() - tim, "seconds.") 

            elif i[0] == "show_formula" and mode == "report":
                if i[1] in self.SFTs:
                    formula = self.SFTs[i[1]].circuit
                elif i[1] in self.clopens:
                    formula = self.clopens[i[1]][2]
                else:
                    raise Exception("No set named %s" % i[1])
                print("Showing compiled formula for %s." % i[1])
                print(formula)
                print()
                
            elif i[0] == "show_parsed" and mode == "report":
                if i[1] in self.SFTs:
                    formula = self.SFTs[i[1]].formula
                elif i[1] in self.clopens:
                    formula = self.clopens[i[1]][2]
                else:
                    raise Exception("No set named %s" % i[1])
                print("Showing parsed formula for %s." % i[1])
                print(formula)
                print()

            elif i[0][:5] == "equal":
                if i[1] in self.SFTs and i[2] in self.SFTs:
                    SFT1 = self.SFTs[i[1]]
                    SFT2 = self.SFTs[i[2]]
                    report_SFT_equal((i[1], SFT1), (i[2], SFT2), mode=mode, truth=i[0][5:])

                elif i[1] in self.CAs and i[2] in self.CAs:
                    CA1 = self.CAs[i[1]]
                    CA2 = self.CAs[i[2]]
                    report_CA_equal((i[1], CA1), (i[2], CA2), mode=mode, truth=i[0][5:])
                
                else:
                    raise Exception("%s or %s is not an SFT." % i[1:])
                
                    #if i[1] not in clopens or i[2] not in clopens:
                    #    raise Exception("%s not a clopen set"i[1] )                
                    #clopen1 = clopens[i[1]]
                    #clopen2 = clopens[i[2]]
                    #raise Exception("Comparison of clopen sets not implemented.")
                    
            elif i[0][:8] == "contains":

                if i[1] in self.SFTs:
                    SFT1 = self.SFTs[i[1]]
                    SFT2 = self.SFTs[i[2]]
                    report_SFT_contains((i[1], SFT1), (i[2], SFT2), mode=mode, truth=i[0][8:])
                else:
                    clopen1 = self.clopens[i[1]]
                    clopen2 = self.clopens[i[2]]
                    raise Exception("Comparison of clopen sets not implemented.")

            elif i[0] == "compare_SFT_pairs" and mode == "report":
                for a in self.SFTs:
                    for b in self.SFTs:
                        if a == b:
                            continue
                        report_SFT_contains((a, self.SFTs[a]), (b, self.SFTs[b]))

            elif i[0] == "compare_SFT_pairs_equality" and mode == "report":
                #print(SFTs_as_list)
                for (i, (aname, a)) in enumerate(self.SFTs.items()):# SFTs_as_list):
                    for (bname, b) in list(self.SFTs.items())[i+1:]: #SFTs_as_list[i+1:]:
                        report_SFT_equal((aname, a), (bname, b))

            elif i[0] == "show_forbidden_patterns":
                
                the_sft = self.SFTs[i[1]]
                print("Showing forbidden patterns for %s." % i[1])
                if the_sft.forbs is None:
                    print("Forbidden patterns not yet computed.")
                else:
                    print(the_sft.forbs)
                print()

            elif i[0] == "compute_forbidden_patterns":
                
                the_sft = self.SFTs[i[1]]
                rad = i[2]
                if mode == "report":
                    print("Computing forbidden patterns for %s using radius %s." % (i[1], rad))
                    if the_sft.forbs is not None:
                        print("It already had forbidden patterns; overwriting them.")
                    print()
                the_sft.deduce_forbs(rad)

            elif i[0] == "set_weights":
                self.weights = i[1]
                print(self.weights)

            elif i[0] == "Wang" or i[0] == "wang":
                name = i[1]
                #print(i[1])
                tiles = i[2]
                kwargs = i[3]
                flags = i[4]
                custom_topology = False

                #print(flags)
                
                # a flag can be used to make this use the current topology
                if flags.get("topology", False) or flags.get("use_topology", False) or \
                   flags.get("custom_topology", False):
                    custom_topology = True
                    raise Exception("Work in progress...")
                    colors, formula = general_Wang(tiles, nodes, topology, kwargs.get("inverses", []))
                # ad hoc code for 2d Wang tiles
                else:
                    colors, formula = basic_2d_Wang(tiles)
                    
                circ = compiler.formula_to_circuit(Wang_nodes, 2, Wang_topology, colors, formula)
                self.SFTs[name] = sft.SFT(2, Wang_nodes, self.alphabet, circuit=circ, formula=formula)

            # caching is global, is that dangerous?
            # in principle we could have a circuitset here in diddy,
            # and (through compiler) tell Circuit that we are using one,
            elif i[0] == "start_cache":
                compiler.start_cache(i[1][0], i[1][1])
            elif i[0] == "end_cache":
                compiler.end_cache()

            elif i[0] == "CA":
                name = i[1]
                rules = i[2]
                circuits = {}
                for r in rules:
                    circ = compiler.formula_to_circuit(self.nodes, self.dim, self.topology, self.alphabet, r[2])
                    circuits[(r[0], r[1])] = circ
                #print(circuits)
                self.CAs[name] = blockmap.CA(self.alphabet, self.nodes, self.dim, circuits)

            elif i[0] == "compose_CA":
                composands = i[1]
                print(composands, self.CAs)
                result_name = composands[0]
                result_CA = self.CAs[composands[1]]
                for name in composands[2:]:
                    result_CA = result_CA.then(self.CAs[name])
                self.CAs[result_name] = result_CA

            elif i[0] == "calculate_CA_ball":
                radius = i[1]
                filename = i[2]
                generators = i[3][0]
                print("Computing relationss for CA %s into file %s." % (str(generators), filename))
                generators = [self.CAs[j] for j in generators]
                with open(filename, "w") as outfile:
                    for output in blockmap.find_relations(generators, radius):
                        if output[0] == "rel":
                            outfile.write("New relation: %s = %s" % output[1:] + "\n")
                        else:
                            rr = repr(output[1])
                            #print(len(rr), rr)
                            #if len(rr) > 50:
                            #    rr = rr[:47] + "..."
                            #outfile.write("New CA: %s = %s" % (rr, output[2]) + "\n")
        
                            outfile.write("New CA of complexity %s at %s." % (len(rr), output[2]) + "\n")
                #blockmap.find_relations(generatrs
                #                        )
                                        
            elif mode == "report":
                raise Exception("Unknown command %s." % i[0])


# for a dict with lists on the right, return all sections
def get_sections(dicto):
    #print(dicto)
    # get an arbitrary key
    if len(dicto) == 0:
        yield {}
        return
    it = next(iter(dicto.items()))
    # remove it
    rest = dict(dicto)
    del rest[it]
    # recursive solution
    for val in dicto[it]:
        for sec in get_sections(rest):
            sect = dict(sec)
            sect[it] = val
            yield sect

# for each node, give the names of edges into it, and out of it, in order...
def get_in_out_edges(topology):
    in_edges = {}
    out_edges = {}
    for t in topology:
        name, a, b = t
        print(a, b)
        if a[-1] not in out_edges:
            out_edges[a[-1]] = []
        out_edges[a[-1]].append(name)
        if b[-1] not in in_edges:
            in_edges[b[-1]] = []
        in_edges[b[-1]].append(name)
    return in_edges, out_edges

# generate Wang tile SFT for the given topology...
# this variant makes an explicit alphabet with a symbol for each Wang tile
def general_Wang(tiles, nodes, topology, inverses):
    raise Exception("I ran out of steam.")
    # variables for symbols
    var_ranges = {}
    # for each node the variables usable there
    node_tiles = {}

    in_edges, out_edges = get_in_out_edges(topology)

    # the inverses list is used as the default order for directions
    directions = []
    for dd in inverses:
        directions.append(dd[0])
        directions.append(dd[1])
        
    # given a tile as a tuple, return tile as dict
    def fix_for_node(node, tile):
        #print(node, tile,out_edges)
        assert len(tile) == len(out_edges[node])

        tile_colors = {}
        remaining_colors = []
        used_directions = set()
        for t in tile:
            if type(t) == tuple and t[0] == "SET":
                tile_colors[t[1]] = t[2]
                used_directions.add(t[1])
            else:
                #raise Exception("non-kw wangs not implemented yet")
                remaining_colors.append(t)
                
        i = 0
        for d in directions:
            if d in out_edges[node]:
                if d not in used_directions:
                    tile_colors[d] = remaining_colors[i]
                    i += 1
        return tile_colors
            
    for t in tiles:
        if t[0] == ["variable"]:
            var_ranges[t[1]] = t[2]
        else:
            if type(t[0]) == list:
                node_list = t[0]
                tile = t[1:]
            else:
                node_list = nodes
                tile = t
            for n in node_list:
                if n not in node_tiles:
                    node_tiles[n] = []
                node_tiles[n].append(fix_for_node(n, tile))
    
    inverses_dict = {}
    all_seen = set()
    for k in inverses:
        inverses_dict[k[0]] = k[1]
        all_seen.add(k[0])
        all_seen.add(k[1])

    # we want that an inverse is specified for all  
    assert all_seen == set([t[0] for t in topology])

    actual_tiles_per_node = {}
    for n in nodes:
        actual_tiles_per_node[n] = []
        for t in node_tiles[n]:
            interesting_ranges = {}
            for c in t:
                if t[c] in var_ranges:
                    interesting_ranges[t[c]] = var_ranges[t[c]]
            for var_vals in get_sections(interesting_ranges):
                actual_tile = {}
                for c in t:
                    if t[c] in var_ranges:
                        val = var_vals[t[c]]
                    else:
                        val = t[c]
                    actual_tile[c] = val
                actual_tiles_per_node[n].append(actual_tile)
                    
    # print(actual_tiles_per_node)

    formula = "Ao \n"
    # for each positive direction, require that ugh...
    for n in nodes:
        nodeformula = "o = o.%s -> (\n" % n
        
        for d in inverses_dict:
            pass
        for t in topology:
            if t[-1] == None:
                pass
            

# given list of tiles, return colors and formula
def basic_2d_Wang(tiles):
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
    print("Testing whether SFTs %s and %s are equal." % (aname, bname))
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

def report_CA_equal(a, b, mode="report", truth=True):
    aname, aCA = a
    bname, bCA = b
    print("Testing whether CA %s and %s are equal." % (aname, bname))
    tim = time.time()
    res = aCA == bCA
    tim = time.time() - tim
    if res: 
        print("They are EQUAL (time %s)." % (tim))
    else:
        print("They are DIFFERENT (time %s)." % (tim))
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




if __name__ == "__main__":
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument("filename", metavar='f', type=str)
    args = arg_parser.parse_args()

    with open(args.filename, 'r') as f:
        code = f.read()

    run_diddy(code)

    
