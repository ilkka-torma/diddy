
from general import *
import collections
import sft

# Much of this is copied from period_automaton with minor modifications
# TODO: unify the common parts?

def words(length, trans_alph, nodes, forbs):
    if not length:
        yield tuple()
    else:
        for word in words(length-1, trans_alph, nodes, forbs):
            for syms in trans_alph:
                word2 = (syms,) + word
                if all(any(forb.get((i, node), sym) != sym
                           for (i, syms2) in enumerate(word2)
                           for (sym, node) in zip(syms2, nodes))
                       for forb in forbs
                       if len(forb) <= length):
                    yield word2
                    
def remove_sinks(trans, alph, sources_too=False, verbose=False):
    i = 1
    if verbose:
        print("Trimming automaton with {} transitions.".format(len(trans)))
    
    size = len(trans)
    while True:
        not_sink = set()
        not_source = set()
        for ((st, sym), st2) in trans.items():
            not_sink.add(st)
            not_source.add(st2)
        trans = {(st, sym) : st2
                 for ((st, sym), st2) in trans.items()
                 if st in not_sink
                 if not sources_too or st2 in not_source}
        if verbose:
            print("Round {}: {} transitions left.".format(i, len(trans)))
            i += 1
        new_size = len(trans)
        if new_size == size:
            break
        size = new_size
    return trans

class Sofic1D:
    """
    A finite automaton representing a 1D sofic shift. May or may not be right resolving.
    The main data is trans, which is:
    a) a dict[state, sym] -> state if right resolving, or
    b) a dict[state, sym] -> set(state) if not.
    sym here is a tuple of symbols, one for each node
    """
    
    def __init__(self, nodes, alph, topology, trans, right_resolving=False, onesided=False):
        self.dim = 1
        self.nodes = nodes
        self.alph = alph
        self.trans_alph = list(iter_prod(*(iter(alph[node]) for node in nodes)))
        self.topology = topology
        self.trans = trans
        self.states = set(tr[0] for tr in self.trans)
        self.right_resolving = right_resolving
        self.onesided = onesided
        self.minimal = False
        
    @classmethod
    def from_SFT(cls, the_sft, verbose=False):
        "Construct a 1D sofic shift from a 1D SFT using forbidden patterns."
        assert the_sft.dim == 1
        assert the_sft.forbs is not None
        if verbose:
            print("Constructing sofic automaton.")
        trans_alph = list(iter_prod(*(iter(the_sft.alph[node]) for node in the_sft.nodes)))
        forbs = []
        for forb_pat in the_sft.forbs:
            min_ix = min(nvec[0] for nvec in forb_pat)
            forbs.append({(i-min_ix, n) : c for ((i,n),c) in forb_pat.items()})
        max_len = max(nvec[0] for forb in forbs for nvec in forb)
        trans_words = set(words(max_len+1, trans_alph, the_sft.nodes, forbs))
        trans = {(word[:-1], word[-1]) : word[1:]
                 for word in trans_words}
        trans = remove_sinks(trans, trans_alph, sources_too = 0 not in the_sft.onesided, verbose=verbose)
        return cls(the_sft.nodes, the_sft.alph, the_sft.topology, trans, right_resolving=True, onesided = the_sft.onesided==[0])
        
    def determinize(self, verbose=False, trim=True):
        "Determinize this automaton using the powerset construction."
        assert not self.right_resolving
        
        # Maintain sets of seen and unprocessed state sets, and integer labels for seen sets
        if verbose:
            print("Determinizing automaton with {} states and {} transitions".format(len(self.states), len(self.trans)))
        
        init_st = frozenset(self.states)
        seen = {init_st : 0}
        frontier = collections.deque([(init_st, 0)])
        
        det_trans = {}
        num_seen = 1
        
        i = 1
        k = 0
        while frontier:
            if verbose:
                i -= 1
                if i == 0:
                    k += 1
                    print("{}: {} states found.".format(k,num_seen))
                    i = len(frontier)
                
            # Pick an unprocessed state set, go over its successors
            st_set, st_num = frontier.popleft()
            for sym in self.trans_alph:
                new_st_set = frozenset(st2 for st in st_set for st2 in self.trans.get((st, sym), set()))
                if new_st_set:
                    try:
                        # Use existing label
                        new_num = seen[new_st_set]
                    except KeyError:
                        # Pick a new label for the set
                        new_num = num_seen
                        num_seen += 1
                        frontier.append((new_st_set, new_num))
                        seen[new_st_set] = new_num
                    # Transitions are stored using the integer labels
                    det_trans[st_num, sym] = new_num
        
        # Trim the transitions
        if trim:
            det_trans = remove_sinks(det_trans, self.trans_alph, sources_too=not self.onesided)

        self.trans = det_trans
        self.states = set(tr[0] for tr in det_trans)
        self.right_resolving = True
        
        if verbose:
            print("Determinized to {} states and {} transitions".format(len(self.states), len(self.trans)))
        
    def minimize(self, verbose=False):
        "Minimize this right-resolving automaton using Moore's algorithm."
        assert self.right_resolving
        if self.minimal:
            return

        # Start with uniform color
        # 0 is the special "no state" color
        coloring = {st : 1 for st in self.states}
        colors = set([1])
        num_colors = 1
        
        # Iteratively update coloring based on the colors of successors
        i = 0
        while True:
            if verbose:
                i += 1
                print("Minimization round {}: {} states separated.".format(i, num_colors))
            # First, use tuples of colors as new colors
            new_coloring = dict()
            new_colors = set()
            for st in self.states:
                next_colors = [coloring[st]]
                for sym in self.trans_alph:
                    try:
                        next_colors.append(coloring[self.trans[st, sym]])
                    except KeyError:
                        next_colors.append(0)
                new_color = tuple(next_colors)
                new_coloring[st] = new_color
                new_colors.add(new_color)
            # Then, encode new colors as positive integers
            color_nums = { color : i for (i, color) in enumerate(new_colors, start=1) }
            new_coloring = { st : color_nums[color] for (st, color) in new_coloring.items() }
            new_num_colors = len(new_colors)
            # If strictly more colors were needed, repeat
            if num_colors == new_num_colors:
                break
            else:
                colors = new_colors
                coloring = new_coloring
                num_colors = new_num_colors

        # Compute new transition function and state set
        self.trans = {(coloring[st]-1, sym) : coloring[st2]-1
                      for ((st, sym), st2) in self.trans.items()}
        self.states = set(tr[0] for tr in self.trans)
        self.minimal = True
        
    def intersection(self, other):
        "Intersection of two 1D sofics."
        assert self.nodes == other.nodes and self.alph == other.alph and self.onesided == other.onesided
        if self.right_resolving:
            if other.right_resolving:
                trans = {((st1, st2), sym) : (res1, other.trans[st2, sym])
                         for ((st1, sym), res1) in self.trans.items()
                         for st2 in other.states
                         if (st2, sym) in other.trans}
            else:
                trans = {((st1, st2), sym) : set((res1, res2) for res2 in other.trans[st2, sym])
                         for ((st1, sym), res1) in self.trans.items()
                         for st2 in other.states
                         if (st2, sym) in other.trans}
        elif other.right_resolving:
            trans = {((st1, st2), sym) : set((res, other.trans[st2, sym]) for res in ress)
                     for ((st1, sym), ress) in self.trans.items()
                     for st2 in other.states
                     if (st2, sym) in other.trans}
        else:
            trans = {((st1, st2), sym) : set((res1, res2) for res1 in ress for res2 in other.trans[st2, sym])
                     for ((st1, sym), ress) in self.trans.items()
                     for st2 in other.states
                     if (st2, sym) in other.trans}
        return Sofic1D(self.nodes, self.alph, self.topology, trans, right_resolving=self.right_resolving and other.right_resolving, onesided=self.onesided)
        
    def union(self, other):
        "Union of two 1D sofic shifts."
        assert self.nodes == other.nodes and self.alph == other.alph and self.onesided == other.onesided
        if self.right_resolving:
            if other.right_resolving:
                trans = {((st,0), sym) : (res,0)
                         for ((st, sym), res) in self.trans.items()}
                trans.update({((st,1), sym) : (res,1)
                              for ((st, sym), res) in other.trans.items()})
            else:
                trans = {((st,0), sym) : set([(res,0)])
                         for ((st, sym), res) in self.trans.items()}
                trans.update({((st,1), sym) : set((res,1) for res in ress)
                              for ((st, sym), ress) in other.trans.items()})
        elif other.right_resolving:
            trans = {((st,0), sym) : set((res,0) for res in ress)
                     for ((st, sym), ress) in self.trans.items()}
            trans.update({((st,1), sym) : set([(res,1)])
                          for ((st, sym), res) in other.trans.items()})
        else:
            trans = {((st,0), sym) : set((res,0) for res in ress)
                     for ((st, sym), ress) in self.trans.items()}
            trans.update({((st,1), sym) : set((res,1) for res in ress)
                          for ((st, sym), ress) in other.trans.items()})
        return Sofic1D(self.nodes, self.alph, self.topology, trans, right_resolving=self.right_resolving and other.right_resolving, onesided=self.onesided)
        
def intersection(*sofics):
    cur = sofics[0]
    for nxt in sofics[1:]:
        cur = cur.intersection(nxt)
    return cur
    
def union(*sofics):
    cur = sofics[0]
    for nxt in sofics[1:]:
        cur = cur.union(nxt)
    return cur