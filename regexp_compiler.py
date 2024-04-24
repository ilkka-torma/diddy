import finite_automata as FA
from general import iter_prod

def compile_regexp(nodes, node_alph, regexp):
    "Compile a regex into a finite automaton"
    # Same cell alphabet as in 1D sofic shifts: tuples with one symbol per node
    cell_alph = list(iter_prod(*(iter(node_alph[node]) for node in nodes)))
    return compile_regexp_(cell_alph, regexp)

def compile_regexp_(alph, regexp):
    #print("compiling", alph, regexp)
    if regexp == "EMPTYWORD":
        ret = FA.NFA.empty_word(alph)
    elif regexp[0] == "WORD":
        # regexp[1] is a list of "symbols" to be concatenated, consisting of
        # (a) ("SYMBOL", sym), which is to be interpreted as (sym,)
        # (b) ("SYMBOLS", syms), which is to be interpreted as tuple(syms)
        word = []
        for (label, sym) in regexp[1]:
            if label == "SYMBOL":
                word.append((sym,))
            elif label == "SYMBOLS":
                word.append(tuple(sym))
            else:
                raise Exception("Unexpected regex label: {}".format(label))
        ret = FA.NFA.single_word(alph, word)
    elif regexp[0] == "UNION":
        aut1 = compile_regexp_(alph, regexp[1])
        aut2 = compile_regexp_(alph, regexp[2])
        ret = aut1.union(aut2)
        ret.rename()
    elif regexp[0] == "ISECT":
        aut1 = compile_regexp_(alph, regexp[1])
        aut2 = compile_regexp_(alph, regexp[2])
        ret = aut1.intersect(aut2)
        ret.rename()
    elif regexp[0] == "CONCAT":
        aut1 = compile_regexp_(alph, regexp[1])
        aut2 = compile_regexp_(alph, regexp[2])
        ret = aut1.concat(aut2)
        ret.rename()
    elif regexp[0] == "STAR":
        aut = compile_regexp_(alph, regexp[1])
        ret = aut.star()
    elif regexp[0] == "PLUS":
        aut = compile_regexp_(alph, regexp[1])
        ret = aut.plus()
    #print("compiled", regexp, "into", ret.trans)
    return ret