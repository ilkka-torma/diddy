
from general import *
from configuration import RecognizableConf
import collections
import sft
from itertools import combinations

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
        
    def equals(self, other, return_radius=True, method=None, verbose=False):
        "If this 1d sofic equal to the other?"
        assert self.minimal
        assert isinstance(other, Sofic1D)
        assert other.minimal
        
        # check number of states and transitions
        if verbose:
            print("checking sizes of automata")
        if len(self.states) != len(other.states):
            if return_radius:
                return False, None
            else:
                return False
        if len(self.trans) != len(other.trans):
            if return_radius:
                return False, None
            else:
                return False
        
        # compute separating words (positive and negative followers for each state)
        if verbose:
            print("computing followers")
        followers = {st : [set(), set()] for st in self.states}
        for (st1, st2) in combinations(self.states, 2):
            # if the states are already separate, do nothing
            if followers[st1][0] & followers[st2][1] or followers[st1][1] & followers[st2][0]:
                continue
            # separate these states
            states1 = {tuple() : st1}
            states2 = {tuple() : st2}
            n = 0
            while True:
                n += 1
                new_states1 = dict()
                new_states2 = dict()
                for (word, state1) in states1.items():
                    state2 = states2[word]
                    for sym in self.trans_alph:
                        new1 = self.trans.get((state1, sym), None)
                        new2 = self.trans.get((state2, sym), None)
                        new_word = word + (sym,)
                        if new1 is None:
                            if new2 is not None:
                                followers[st1][1].add(new_word)
                                followers[st2][0].add(new_word)
                                break
                        elif new2 is None:
                            followers[st1][0].add(new_word)
                            followers[st2][1].add(new_word)
                            break
                        else:
                            new_states1[new_word] = new1
                            new_states2[new_word] = new2
                    else:
                        continue
                    break
                else:
                    states1.update(new_states1)
                    states2.update(new_states2)
                    continue
                break
        
        # match the states
        if verbose:
            print("matching states")
        match = dict()
        for other_st in other.states:
            for (st, [poss, negs]) in followers.items():
                if st not in match:
                    for word in poss:
                        cur = other_st
                        for sym in word:
                            try:
                                cur = other.trans[cur, sym]
                            except KeyError:
                                break
                        else:
                            continue
                        break
                    else:
                        for word in negs:
                            cur = other_st
                            for sym in word:
                                try:
                                    cur = other.trans[cur, sym]
                                except KeyError:
                                    break
                            else:
                                break                                
                        else:
                            match[st] = other_st
                            break
        
        # check for isomorphism of automata (note that they have equally many transitions)
        if verbose:
            print("checking for isomorphism")
        for ((st, sym), st2) in self.trans.items():
            if other.trans.get((match[st],sym), None) != match[st2]:
                if return_radius:
                    return False, None
                else:
                    return False
        if return_radius:
            return True, None
        else:
            return True
            
        
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
                    
    def deduce_transition(self, conf_word, fixed_axes, st1=None, st2=None, equal=False):
        "Deduce transition words and pairs along the finite/periodic word"
        period = len(conf_word)
        pairs = {(st, st) : tuple()
                 for st in (self.states if st1 is None else [st1])}
        word_len = 0
        seen = set()
        while pairs:
            found_new = False
            # extend the words by a single symbol of the periodic word
            conf_syms = conf_word[word_len % period]
            if None in conf_syms:
                # nonexistent node -> put arbitrary symbols, restart from arbitrary state
                new_pairs = dict()
                for ((st, stt), word) in pairs.items():
                    new_sym = tuple(min(sym) if type(sym) == list else sym for sym in conf_syms)
                    for new_st in self.states:
                        new_pairs[st, new_st] = word + (new_sym,)
            else:
                # all nodes exist -> compute new states
                new_pairs = dict()
                for ((st, stt), word) in pairs.items():
                    for sym in iter_prod(*(iter(syms if type(syms) == list else [syms])
                                           for syms in conf_syms)):
                        try:
                            new_st = self.trans[stt, sym]
                            new_pairs[st, new_st] = word+(sym,)
                        except KeyError:
                            pass
            pairs = new_pairs
            word_len += 1
            if word_len % period == 0:
                # check if we have found a configuration
                for ((st, stt), word) in pairs.items():
                    if (st, stt) not in seen:
                        seen.add((st, stt))
                        found_new = True
                        if (st1 is None or st == st1) and (st2 is None or stt == st2) and (st == stt or not equal):
                            # transition was found
                            yield (st, stt, word)
                if fixed_axes or not found_new:
                    # no configuration was found
                    break
        
    def deduce_global(self, conf, periodics=None, fixed_axes=None, bound=None):
        "Deduce a global configuration with variable structure."
        assert self.right_resolving # for now
        
        # conf is a recognizable configuration
        # periodics is a list of directions we want to be periodic (either [] or [0])
        # fixed_axes is a list of directions where we have fixed the markers (either [] or [0])
        
        [(a,b,c,d)] = conf.markers
        if a==b and c==d:
            # periodic configuration
            period = c-a
            conf_word = [tuple(conf[a+i,node] for node in self.nodes)
                         for i in range(period)]
            # find periodic result (since one must exist, if a result exists)
            for (st, stt, word) in self.deduce_transition(conf_word, fixed_axes, equal=True):
                word_len = len(word)
                markers = [(a,a, a+word_len, a+word_len)]
                pat = {(a+i, node) : sym
                       for (i, syms) in enumerate(word)
                       for (node, sym) in zip(self.nodes, syms)}
                return RecognizableConf(markers, pat, self.nodes, onesided=self.onesided)
        else:
            # general recognizable configuration
            # first find all possible periodic tails
            left_per = [tuple(conf[a+i,node] for node in self.nodes) for i in range(b-a)]
            middle = [tuple(conf[i,node] for node in self.nodes) for i in range(b,c)]
            right_per = [tuple(conf[c+i,node] for node in self.nodes) for i in range(d-c)]
            
            if self.onesided:
                left_per_tails = {st : tuple() for st in self.states}
            else:
                left_per_tails = {st : per
                                  for (st, _, per) in self.deduce_transition(left_per, fixed_axes, equal=True)}
            if fixed_axes:
                left_tails = {st : (per, tuple())
                              for (st, per) in left_per_tails.items()}
            else:
                left_tails = {st : (per, trans)
                              for (lst, per) in left_per_tails.items()
                              for (_, st, trans) in self.deduce_transition(left_per, False, st1=lst)}
            left_mids = {st : (per, trans, mid)
                         for (lst, (per, trans)) in left_tails.items()
                         for (_, st, mid) in self.deduce_transition(middle, True, st1=lst)}
            if fixed_axes:
                right_trans = left_mids
            else:
                right_trans = {st : (per, ltrans, mid+trans)
                         for (lst, (per, ltrans, mid)) in left_mids.items()
                         for (_, st, trans) in self.deduce_transition(right_per, False, st1=lst)}
            for (lst, (lper, ltrans, rtrans)) in right_trans.items():
                for (_, _, rper) in self.deduce_transition(right_per, fixed_axes, st1=lst, st2=lst):
                    # we have found the configuration
                    marker = (b-len(lper)-len(ltrans), b-len(ltrans), b+len(rtrans), b+len(rtrans)+len(rper))
                    pat = dict()
                    for (i, syms) in enumerate(lper + ltrans + rtrans + rper):
                        for (node, sym) in zip(self.nodes, syms):
                            pat[marker[0]+i, node] = sym
                    return RecognizableConf([marker], pat, self.nodes, onesided=self.onesided)
        return None
            
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