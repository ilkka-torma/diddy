import finite_automata as FA
from general import iter_prod

def compile_regexp(nodes, node_alph, regexp, verbose=False):
    "Compile a regex into a finite automaton"
    if verbose:
        print("Compiling regexp", regexp)
    # Same cell alphabet as in 1D sofic shifts: tuples with one symbol per node
    cell_alph = list(iter_prod(*(iter(node_alph[node]) for node in nodes)))
    return compile_regexp_(cell_alph, regexp)

def compile_regexp_(alph, regexp):
    #print("compiling", alph, regexp)
    if regexp == "EMPTYWORD":
        ret = FA.NFA.empty_word(alph)
    elif regexp[0] == "SYMBOL":
        ret = FA.NFA.singleton(alph, (regexp[1],))
    elif regexp[0] == "SYMBOLS":
        ret = FA.NFA.singleton(alph, tuple(regexp[1]))
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
    elif regexp[0] == "CONTAINS":
        aut = compile_regexp_(alph, regexp[1])
        any_aut = FA.DFA.universal(alph)
        ret = any_aut.concat(aut).concat(any_aut)
        ret.rename()
    elif regexp[0] == "NOT":
        aut = compile_regexp_(alph, regexp[1])
        if isinstance(aut, FA.NFA):
            aut = aut.determinize().minimize()
        ret = aut.negate()
    elif regexp[0] == "STAR":
        aut = compile_regexp_(alph, regexp[1])
        ret = aut.star()
    elif regexp[0] == "PLUS":
        aut = compile_regexp_(alph, regexp[1])
        ret = aut.plus()
    else:
        raise Exception("Unknown regexp command: {}".format(regexp[0]))
    #print("compiled", regexp, "into", ret.trans)
    return ret
