from pysat.solvers import Glucose4
from circuit import *

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

# return an equivalence relation on the vertices of a circuit, plus inverses
# the relation is given as dict[node-id : frozenset[node-id]]
# the inverses are given as dict[node-id : None or frozenset[node-id]]
def circuit_eq_rel_and_inv(circ):
    var_to_name = dict()
    inst, next_name = circuit_to_sat_instance(circ, var_to_name)
    name_to_var = {name:var for (var,name) in var_to_name.items()}
    rel, inv = compute_eq_relation_and_inverses(inst)# + [[var_to_name[circ.get_id()]]])
    #print("instance relation", rel)
    circ_rel = {name_to_var[var] : frozenset(name_to_var[var2] for var2 in cls)
                for cls in rel
                for var in cls}
    for node in circ.internal_nodes(vars_too=True):
        the_id = node.get_id()
        if the_id not in circ_rel:
            circ_rel[the_id] = {node.get_id()}
    circ_inv = {name_to_var[var] : (None if inv is None else frozenset(name_to_var[var2] for var2 in inv))
                for (cls, inv) in inv.items()
                for var in cls}
    return circ_rel, circ_inv

# compute an equivalent circuit using equivalence relations, and its old id
def simplify_circ_eqrel(circ, seen=None, circ_rel=None, circ_inv=None, idmap=None):
    if seen is None:
        seen = dict()
    if circ_rel is None:
        circ_rel, circ_inv = circuit_eq_rel_and_inv(circ)
    if idmap is None:
        idmap = dict()
        for node in circ.internal_nodes(vars_too=True):
            idmap[node.get_id()] = node
    the_id = circ.get_id()
    # idmap is dict[id] -> set(circ)
    # circ_rel is dict[id] -> set[id]
    # seen is dict[id] -> circ
    #print("circ", circ, "the id", the_id, "idmap", idmap, "circ rel", circ_rel, "seen", seen)
    if the_id in seen:
        return the_id, seen[the_id]
    #seen[the_id] = circ
    new_inputs = []
    new_ids = set()
    min_eq = idmap[min(circ_rel[the_id],
                       key=lambda i: sum(1 for _ in idmap[i].internal_nodes(vars_too=True)))]
    for eq_id in circ_rel[the_id]:
        seen[eq_id] = min_eq
    if circ.op in "FTV":
        ret = circ
    elif circ.op == "&":
        for input in circ.inputs:
            input_id = input.get_id()
            if any(var in new_ids for var in circ_rel[input_id]):
                # positive instance found -> skip
                continue
            if any(var in new_ids for var in circ_inv[input_id] or set()):
                # negative instance found -> make F
                #print("found neg")
                ret = F
                break
            # else simplify and append
            new_inputs.append(simplify_circ_eqrel(input, seen, circ_rel, circ_inv, idmap)[1])
            new_ids.add(input_id)
        else:
            ret = AND(*new_inputs)
    elif circ.op == "|":
        for input in circ.inputs:
            input_id = input.get_id()
            if any(var in new_ids for var in circ_rel[input_id]):
                # positive instance found -> skip
                continue
            if any(var in new_ids for var in circ_inv[input_id] or set()):
                # negative instance found -> make T
                ret = T
                break
            # else simplify and append
            new_inputs.append(simplify_circ_eqrel(input, seen, circ_rel, circ_inv, idmap)[1])
            new_ids.add(input_id)
        else:
            ret = OR(*new_inputs)
    elif circ.op == "!":
        input = circ.inputs[0]
        input_id = input.get_id()
        inv = circ_inv[input_id]
        if inv is None:
            ret = NOT(simplify_circ_eqrel(input, seen, circ_rel, circ_inv, idmap)[1])
        else:
            the_id, ret = simplify_circ_eqrel(idmap[min(inv)], seen, circ_rel, circ_inv, idmap)
    for eq_id in circ_rel[the_id]:
        seen[eq_id] = ret
    return the_id, ret
    
# simplify a conjunction of translates of the circuit
# global_vecs is the set of translates
# local_vecs is the set of pairwise translates we jointly simplify (default is -nhood)
# NOTE: incomplete
def simplify_translates_eqrel(circ, vecs, local_vecs=None, seen=None, circ_rel=None, circ_inv=None, idmap=None):
    raise NotImplementedError("simplify_translates_eqrel not implemented")
    if local_vecs is None:
        local_vecs = set(vneg(var[:-2]) for var in circ.get_variables())
    local_rel_inv = dict()
    for vec in local_vecs:
        circ2 = circ.copy()
        transform(circ2, lambda var: vadd(var[:-2], vec) + var[-2:])
        conj = AND(circ, circ2)
        idmap = dict()
        for node in conj.internal_nodes(vars_too=True):
            idmap[node.get_id()] = node
        rel, inv = circuit_eq_rel_and_inv(conj)
        rel = {idmap[the_id] : idmap[min(ids,
                                     key=lambda i: sum(1 for _ in idmap[i].internal_nodes()))]
               for (the_id, ids) in rel.items()}
        inv = {idmap[the_id] : None if ids is None
                               else idmap[min(ids,
                                              key=lambda i: sum(1 for _ in idmap[i].internal_nodes()))]
               for (the_id, ids) in inv.items()}
        # TODO: replace rel and inv with dicts that give a substitution
        local_rel_inv[vec] = (rel, inv)
    global_circs = dict()
    for vec in global_vecs:
        circ2 = circ.copy()
        transform(circ2, lambda var: vadd(var[:-2], vec) + var[-2:])
        global_circs[vec] = circ2
    # simplify iteratively until nothing changes
    domain = set(global_vecs)
    while domain:
        for vec in domain:
            for (tr_vec, (rel, inv)) in local_rel_inv.items():
                if vadd(vec, tr_vec) in global_vecs:
                    for the_vec in [vec, tr_vec]:
                        the_circ = global_circs[the_vec]
                        

"""
#inst = [[1,2,3], [2, 3], [1, 3], [2, 1], [-2]] #, [1, 4], [-1, -4], [2, 5], [-2, -5]] #[[1, 2], [-2, -1]]
#print(compute_eq_relation_and_inverses(inst))
circ1 = OR(AND(V(2), V(4), V(3)), AND(V(2), OR(NOT(V(1)), V(3)), V(1)), AND(NOT(V(2)), V(3)))
circ2 = circ1.copy()
transform(circ2, lambda n: n+1)
circ3 = circ1.copy()
transform(circ3, lambda n: n+2)
circ = AND(circ1, circ2, circ3)
#rel, inv = circuit_eq_rel_and_inv(circ)
#for (var, cls) in rel.items():
#    print(var, cls)
_, simp = simplify_circ_eqrel(circ)
#print(simp)
simp.simplify()
#print(simp)
print("from", sum(1 for _ in circ.internal_nodes(vars_too=True)), "to", sum(1 for _ in simp.internal_nodes(vars_too=True)))
"""