from pysat.solvers import Glucose4

"""
Given a SAT instance, compute the equivalence relation on the variables.
"""


def vars_from_SAT_instance(instance):
    variables = set()
    max_var = -1
    for l in instance:
        for v in l:
            variables.add(abs(v))
        max_var = max(max_var, abs(v))
    return variables, max_var

# instance is a SAT instance in the usual format of lists of lists of signed numbers
# return a set of frozensets representing a partition, and
# a dict giving inverse relation between variables
def compute_eq_relation_and_inverses(instance):
    variables, max_var = vars_from_SAT_instance(instance)
    # the inverse pair of v will be max_var + v
    inverse_clauses = []
    new_variables = []
    for v in variables:
        inverse_clauses.append([v, max_var+v])
        inverse_clauses.append([-v, -max_var-v])
        new_variables.append(v)
        new_variables.append(max_var + v)
    eq_rel = compute_eq_relation(instance + inverse_clauses, new_variables)
    #print(eq_rel)
    # we remove inverse variables from all blocks, and calculate inverses of blocks
    invless_eq_rel = set()
    inverses = {}
    for block in eq_rel:
        posblock = set()
        negblock = set()
        for b in block:
            if b <= max_var:
                posblock.add(b)
            else:
                negblock.add(b-max_var)
        invless_eq_rel.add(frozenset(posblock))
        inverses[frozenset(posblock)] = None
        if negblock != set():
            inverses[frozenset(posblock)] = negblock # this will be an actual block of the eq relation
    return invless_eq_rel, inverses

# instance is a SAT instance in the usual format of lists of lists of signed numbers
# return a set of frozensets representing a partition
def compute_eq_relation(instance, variables=None):
    #print(instance,variables)
    #a = bb
    if variables == None: variables, _ = vars_from_SAT_instance(instance)
    bre = split_variables(instance, variables)
    if bre == None: # all variables in the list are actually equivalent
        return set([frozenset(variables)])
    A, B = bre
    #print(A, B, "split")
    eqA = compute_eq_relation(instance, A)
    eqB = compute_eq_relation(instance, B)
    return eqA | eqB 
    
# return an equivalence relation on clique, which
# upper bounds the true eq rel of the instance on clique,
# and separates the clique in two; or None
def split_variables(instance, clique):
    #print("splitting", clique)
    instance = list(instance)
    # force that one is negative, and one is positive
    instance.append(clique)
    instance.append([-i for i in clique])
    with Glucose4(bootstrap_with=instance) as s:
        while s.solve():
            m = s.get_model()
            #print(m)
            positives = set()
            negatives = set()
            for v in m:
                if abs(v) not in clique:
                    continue
                if v > 0:
                    positives.add(abs(v))
                else:
                    negatives.add(abs(v))
            #print("split is", positives, negatives)
            return positives, negatives
    return None

#inst = [[1,2,3], [2, 3], [1, 3], [2, 1], [-2]] #, [1, 4], [-1, -4], [2, 5], [-2, -5]] #[[1, 2], [-2, -1]]
#print(compute_eq_relation_and_inverses(inst))
