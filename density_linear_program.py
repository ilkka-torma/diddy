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
def surroundings(the_sft, vecs, domain, patterns, radius, bigpat=None):
    if bigpat is None:
        # decide on origin
        for fr_pat in patterns:
            for surr in surroundings(the_sft, vecs, domain, patterns, radius, bigpat=dict(fr_pat)):
                surr[(0,)*the_sft.dim] = fr_pat
                yield surr
    else:
        if vecs:
            sft_vars = circuit.get_vars(the_sft.circuit)
            vec = vecs[0]
            shifted_domain = [nvadd(nvec, vec) for nvec in domain]
            for new_bigpat in the_sft.all_patterns(shifted_domain, existing=bigpat, extra_rad=radius):
                backshifted = fd.frozendict({nvsub(pvec, vec) : new_bigpat[pvec] for pvec in shifted_domain})
                for surr in surroundings(the_sft, vecs[1:], domain, patterns, radius, new_bigpat):
                    surr[vec] = backshifted
                    yield surr
        else:
            yield dict()

# given sft, vectors along which to share charge, and patterns that guide the sharing, find best provable lower bound
# vectors is a list of Z^d-vectors that should not contain origin
# patterns is a list of patterns that form a partition of the sft
# each pattern should contain all nodes at origin
# nodes' weights are averaged together for the purposes of charge sharing
def optimal_density(the_sft, vectors, domain, radius, weights=None, ret_shares=False, verbose=False):
    if weights is None:
        weights = {a:a for a in the_sft.alph}
    if verbose:
        print("Lower-bounding density using vectors {} and neighborhood {}".format(vectors, domain))
    # this is how large density can be made, i.e. what we want to compute
    density = pulp.LpVariable("epsilon",
                              min(weights.values()),
                              max(weights.values()))

    # we simply try to maximize this density in our problem
    prob = pulp.LpProblem("discharge", pulp.LpMaximize)
    prob += density

    if verbose:
        print("Computing patterns at origin")
    patterns = set()
    i = 0
    for pat in the_sft.all_patterns(domain):
        patterns.add(fd.frozendict(pat))
        i += 1
        if i%10 == 0:
            print("{} found so far".format(i))
    print("Done with {} patterns".format(i))

    # create variables for how much is discharged in each direction from each pattern
    i = 0
    send = {}
    for vec in vectors:
        for fr_pat in patterns:
            # assert p[(0,0)] == 1
            # send at most everything away
            send[fr_pat, vec] = pulp.LpVariable("patvec{}".format(i)) #, 0, 1)
            i += 1
    if verbose:
        print("Adding constraints")

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
    for surr in surroundings(the_sft, [vneg(vec) for vec in vectors], domain, patterns, radius):

        # for each legal combo, sum the contributions from each -v
        summa = 0
        orig_pat = surr[(0,)*the_sft.dim]
        #print("orig_pat", orig_pat)
        for node in the_sft.nodes:
            summa += weights[orig_pat[(0,)*the_sft.dim + (node,)]] / len(the_sft.nodes)
        for vec in vectors:
            summa -= send[orig_pat, vec]
            pat = surr[vneg(vec)]
            summa += send[pat, vec]
            
        prob += summa >= density
        i += 1
        if verbose and i%50 == 0:
            print("{} found so far".format(i))
    if verbose:
        print("Done with {} constraints, now solving linear program".format(i))

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
    domain = [(0,0,0),(-1,0,0),(0,-1,0),(0,1,0),(1,0,0)]
    #patterns = list(sft.all_patterns([(a,b,0) for (a,b) in domain+[(0,0)]]))
    #patterns = pats(set((a,b,0) for (a,b) in domain+[(0,0)]), alph)
    #patterns = [pat for pat in patterns if sft.deduce(pat, set(pat))]
    #print("patterns", len(patterns))
    vecs = [(0,1),(1,0),(-1,0)]
    dens = optimal_density(sft, vecs, domain, 1, verbose=True)
    print("density", dens)
    print("took", time.time() - t, "seconds")
