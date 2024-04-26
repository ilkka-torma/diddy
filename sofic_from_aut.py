import sofic1d
import finite_automata as FA

def nonempty_subsets(the_set):
    if the_set:
        x = min(the_set)
        for sub in nonempty_subsets(the_set - {x}):
            yield sub
            yield sub | {x}
    else:
        yield set()    

def sofic_from_forbs(nodes, alph, topology, aut, onesided=False, verbose=False):
    "Sofic shift defined by regular language of forbidden words"
    if isinstance(aut, FA.DFA):
        aut = aut.to_nfa()
    #nonfinal = aut.states - aut.finals
    trans = dict()
    seen = {frozenset(aut.inits)}
    frontier = list(seen)
    while frontier:
        newfrontier = []
        for sts in frontier:
            for sym in aut.alph:
                step = {st2 for st in sts for st2 in aut(st, sym)}
                if step.isdisjoint(aut.finals):
                    trans[sts, sym] = new = frozenset(step | aut.inits)
                    if new not in seen:
                        seen.add(new)
                        newfrontier.append(new)
        frontier = newfrontier
    sof = sofic1d.Sofic1D(nodes, alph, topology, trans, onesided=onesided, right_resolving=True)
    sof.remove_sinks()
    if verbose:
        print("Created sofic shift with {} states from forbidden regular language.".format(len(sof.states)))
    return sof

def sofic_as_limit(nodes, alph, topology, aut, onesided=False, verbose=False):
    "Sofic shift defined by forbidding all words that cannot be extended arbitrarily far into words of the language"
    if isinstance(aut, FA.DFA):
        aut = aut.to_nfa()
    aut.trim(forward=not onesided)
    sof = sofic1d.Sofic1D(nodes, alph, topology, aut.trans, onesided=onesided)
    sof.remove_sinks()
    if verbose:
        print("Created sofic shift with {} states as limit of regular language.".format(len(sof.states)))
    return sof
