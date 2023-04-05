"""
Functions for computing lower bounds for density by a discharging argument encoded as a linear program. Uses the Pulp library.
"""

import circuit
from sft import SFT, centered_hypercube
from general import *
import pulp
import frozendict as fd
import time


# given sft, vectors and patterns, enumerate combined locally correct patterns that affect origin
# yield values are dicts : nvec -> pat
# they are shared, i.e. should not be modified by the consumer
def surroundings(the_sft, vecs, patterns, radius, bigpat=None):
    if bigpat is None:
        # decide on origin
        for pat in patterns:
            for surr in surroundings(the_sft, vecs, patterns, radius, bigpat=pat.copy()):
                surr[(0,)*the_sft.dim] = fd.frozendict(pat)
                yield surr
    else:
        if vecs:
            sft_vars = circuit.get_vars(the_sft.circuit)
            vec = vecs[0]
            for pat in patterns:
                shifted = {nvsub(pvec, vec) : val for (pvec,val) in pat.items()}
                if all(bigpat.get(svec, val) == val for (svec, val) in shifted.items()):
                    old_domain = set(bigpat)
                    new_domain = set(svec for svec in shifted if svec not in bigpat)
                    bigpat.update(shifted)
                    big_domain = set()
                    for nvec in bigpat:
                        for var in sft_vars:
                            tr_var = vadd(nvec[:-1], var[:-1])
                            if nvec in old_domain and tr_var in new_domain:
                                for tr in centered_hypercube(the_sft.dim, radius):
                                    big_domain.add(nvadd(nvec, tr))
                                break
                            if nvec in shifted and tr_var in old_domain and tr_var not in shifted:
                                for tr in centered_hypercube(the_sft.dim, radius):
                                    big_domain.add(nvadd(nvec, tr))
                                break
                    if the_sft.deduce(bigpat, big_domain) is not None:
                        for surr in surroundings(the_sft, vecs[1:], patterns, radius, bigpat):
                            surr[vec] = fd.frozendict(pat)
                            yield surr
                    for nvec in new_domain:
                        del bigpat[nvec]
        else:
            yield dict()

# given sft, vectors along which to share charge, and patterns that guide the sharing, find best provable lower bound
# vectors is a list of Z^d-vectors that should not contain origin
# patterns is a list of patterns that form a partition of the sft
# each pattern should contain all nodes at origin
# nodes' weights are averaged together for the purposes of charge sharing
def optimal_density(the_sft, vectors, patterns, radius, weights=None, ret_shares=False, verbose=False):
    if weights is None:
        weights = {a:a for a in the_sft.alph}
    if verbose:
        print("Lower-bounding density using {} vectors and {} patterns".format(len(vectors), len(patterns)))
    # this is how large density can be made, i.e. what we want to compute
    density = pulp.LpVariable("epsilon",
                              min(weights.values()),
                              max(weights.values()))

    # we simply try to maximize this density in our problem
    prob = pulp.LpProblem("discharge", pulp.LpMaximize)
    prob += density

    # create variables for how much is discharged in each direction from each pattern
    i = 0
    send = {}
    for vec in vectors:
        for pat in patterns:
            # assert p[(0,0)] == 1
            # send at most everything away
            send[fd.frozendict(pat), vec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
            i += 1
    if verbose:
        print("Theoretical maximum: {} constraints".format(len(patterns)**(len(vectors)+1)))

    # constrain that in every situation we send at most 1-r away from a 1
    # and recall that we use a partition; currently disabled, "sending through"
    """
    for p in patterns:
        summa = 1
        for v in vectors:
            summa -= send[(p, v)]
        prob += summa >= density
    """

    # list all legal combinations of patterns around origin
    i = 0
    for surr in surroundings(the_sft, [vneg(vec) for vec in vectors], patterns, radius):

        # for each legal combo, sum the contributions from each -v
        summa = 0
        orig_pat = surr[(0,)*the_sft.dim]
        for node in the_sft.nodes:
            summa += weights[orig_pat[(0,)*the_sft.dim + (node,)]] / len(the_sft.nodes)
        for vec in vectors:
            summa -= send[orig_pat, vec]
            pat = surr[vneg(vec)]
            summa += send[pat, vec]
            
        prob += summa >= density
        i += 1
        if verbose and i%1000 == 0:
            print("Found {} constraints so far".format(i))
    if verbose:
        print("Found {} constraints in total, now solving".format(i))

    pulp.PULP_CBC_CMD(msg=0).solve(prob)

    if ret_shares:
        return density.varValue, {(x, y.varValue) for (x,y) in send.items()}
    else:
        return density.varValue

if __name__ == "__main__":
    t = time.time()
    nodes = [0]
    alph = [0,1]
    forbs = [{(-1,0,0):0, (0,0,0):0, (1,0,0):0,(0,1,0):0}]
    sft = SFT(2, nodes, alph, forbs=forbs)
    domain = [(-1,0),(0,-1),(0,1),(1,0)]
    #patterns = list(sft.all_patterns([(a,b,0) for (a,b) in domain+[(0,0)]]))
    patterns = pats(set((a,b,0) for (a,b) in domain+[(0,0)]), alph)
    patterns = [pat for pat in patterns if sft.deduce(pat, set(pat))]
    print("patterns", len(patterns))
    vecs = [(0,1),(1,0),(-1,0)]
    dens = optimal_density(sft, vecs, patterns, 0, verbose=True)
    print("density", dens)
    print("took", time.time() - t, "seconds")
