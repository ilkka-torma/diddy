#from circuit import *
import circuit
from circuit import NOT, V, AND, OR, T, F, IMP, IFF, tech_simp
from general import *

"""
# we construct a circuit whose input variables are of the form (u, n)->a --
# or just (u, n) if alphabet is binary -- and which evaluates to true iff, well.

# pos_variables tells us which positions the variables point to... of course
# those positions will correspond to roughly the variables of the actual formula.

# we can also produce auxiliary variables called aux_0, ..., aux_n
# which can be used for variables ranging over symbols <- outdated!!!!!!!!!!!!!

# all_vars is all the variables that we talk about <- IT IS NOT USED FOR ANYTHING

circuit_variables are aa little tricky... they should be functions
"""
def formula_to_circuit_(nodes, dim, topology, alphabet, formula, variables, aux_var, all_vars):
    #print ("formula", formula)
    #print("variables", variables)
    # print ("aux vars", aux_var)
    # print ("alls", all_vars)
    op = formula[0]
    if op == "BOOL":
        ret = variables[formula[1]]
    elif op == "CIRCUIT":
        var = formula[1][0]
        args = formula[1][1:]
        #print(var, "being called with", args)
        #varvar = variables[var]
        arg_names, code, closure = variables[var]
        variables_new = {}
        if len(args) != len(arg_names):
            raise Exception("Wrong number of parameters in call %s." % (str(var) + " " + str(args)))
        #print("rgs", args)
        #print("nems", arg_names)
        for a in closure:
            variables_new[a] = closure[a]
        for i,a in enumerate(arg_names):
            if type(args[i]) != tuple:
                #variables_new[a] = args[i]
                try:
                    pos = eval_to_position(dim, topology, args[i], variables, nodes)
                except KeyError:
                    pos = args[i] # it's actually a value... hopefully!
                variables_new[a] = pos
            # if argument is a formula, we will evaluate it
            else:
                circ = formula_to_circuit_(nodes, dim, topology, alphabet, args[i], variables, aux_var, all_vars)
                variables_new[a] = circ
        """
        for i in args:
            if type(i) == tuple:
                #col = collect_unbound_vars(i)
                col = []
            elif type(i) == list:
                col = [var_of_pos_expr(i)]
            else:
                col = [i]
            for j in col:
                if j in variables:
                    variables_new[j] = variables[j]
        """
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, code, variables_new, aux_var, all_vars)
    elif op in ["CELLFORALL", "CELLEXISTSCELL", "NODEFORALL", "NODEEXISTS"]:
        var = formula[1]
        bound = formula[2]
        if bound == None:
            bound = {}
        rem_formula = formula[3]
        pos_formulas = []
        typ = op[:4]
        op = op[4:]
        #print(var, typ)
        for q in get_area(dim, topology, variables, bound, typ, nodes):
            #print(var, typ, q)
            variables_new = dict(variables)
            variables_new[var] = q
            pos_formulas.append(formula_to_circuit_(nodes, dim, topology, alphabet, rem_formula, variables_new, aux_var, all_vars))
                                    
            #print(q)
        #print(a = bbb)
        if op == "FORALL":
            ret = AND(*pos_formulas)
        elif op == "EXISTS":
            ret = OR(*pos_formulas)
        else:
            raise Exception("what is" + op)
    elif op in ["FORALLVAL", "EXISTSVAL"]:
        valvar = formula[1]
        rem_formula = formula[2]
        val_formulas = []
        for a in variables:
            variables_new = dict(variables)
            variables_new[valvar] = a
            val_formulas.append(formula_to_circuit_(nodes, dim, topology, alphabet, rem_formula, variables_new, aux_var, all_vars))
        if op == "FORALL":
            ret = AND(*pos_formulas)
        elif op == "EXISTS":
            ret = OR(*pos_formulas)
        else:
            raise Exception("what is" + op)
    elif op in "TF":
        if op == "T":
            ret = T
        elif op == "F":
            ret = F
    elif op in ["OR", "AND", "NOT", "IMP", "IFF"]:
        args = formula[1:]
        arg_formulas = []
        for arg in args:
            arg_formulas.append(formula_to_circuit_(nodes, dim, topology, alphabet, arg, variables, aux_var, all_vars))
        if op == "OR":
            ret = OR(*arg_formulas)
        elif op == "AND":
            ret = AND(*arg_formulas)
        if op == "NOT":
            #print ("NOT", arg_formulas[0], NOT(*arg_formulas))
            ret = NOT(*arg_formulas)
        if op == "IMP":
            ret = IMP(*arg_formulas)
        if op == "IFF":
            ret = IFF(*arg_formulas)
    # bool behaves like a circuit variable without variables; more efficient maybe since we just calculate a circuit
    elif op == "SETBOOL":
        #new_var = aux_var[0]
        #aux_var[0] += 1
        var = formula[1]
        form = formula_to_circuit_(nodes, dim, topology, alphabet, formula[2], variables, aux_var, all_vars)
        variables_new = dict(variables)
        variables_new[var] = form
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, formula[3], variables_new, aux_var, all_vars)
    # cvn[var] should be just the code, and a closure
    elif op == "SETCIRCUIT":
        #print("here")
        var = formula[1][0]
        #print(var)
        arg_names = formula[1][1:]
        #print(arg_names)
        circuit_code = formula[2]
        #print("ccode, ", circuit_code)
        unbound_vars = collect_unbound_vars(circuit_code, set(arg_names))
        #print("unbound", unbound_vars)
        ret_code = formula[3]
        closure = {}
        for v in unbound_vars:
            if v in arg_names:
                continue
            closure[v] = variables[v]
        #print(closure)
        variables_new = dict(variables)
        variables_new[var] = (arg_names, circuit_code, closure)
        
        ret = formula_to_circuit_(nodes, dim, topology, alphabet, ret_code, variables_new, aux_var, all_vars)
    elif op == "POSEQ":
        """
        if formula[1] == ["o", "up"]:
            print(pos_variables, nodes)
        else:
            print("waa")
        """
        #print(formula, pos_variables)
        # p1 and p2 must be position expressions
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        ##print("kili", p1)
        ret = None
        if p1 == None:
            ret = F
        all_vars.add(var_of_pos_expr(formula[1]))
        p2 = eval_to_position(dim, topology, formula[2], variables, nodes)
        if p2 == None:
            ret = F
        all_vars.add(var_of_pos_expr(formula[2]))
        if ret == None and p2 == p1:
            ret = T
        else:
            ret = F
    elif op == "HASVAL":
        ret = None
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        if p1 == None:
            ret = F
        all_vars.add(var_of_pos_expr(formula[1]))
        v = formula[2]
        if ret == None:
            #print("here", p1, v, type(v), alphabet)
            if v not in alphabet:
                #print("%s not in", alphabet)
                if v not in variables:
                    raise Exception("%s is not in alphabet nor a variable" % v)
                v = variables[v] # variables can also contain symbols
            if v == alphabet[0]:
                ret = AND(*(NOT(V(p1 + (sym,))) for sym in alphabet[1:]))
            else:
                ret = V(p1 + (v,))
    # the idea was that we would use hasval when we want to directly
    elif op == "VALEQ":
        ret = None

        p1ispos = True
        try: # horrible hack
            p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
            if p1 == None:
                ret = F
            # evaluates to cell
            if len(p1) != dim+1:
                raise Exception("Cannot compare value of cell, only node.")
        except KeyError:
            p1ispos = False
            #print(formula[1], "formula 1 fast")
            p1val = variables[formula[1]] # we assume the keyerror is because this is symbol variable
        #all_vars.add(var_of_pos_expr(formula[1]))

        p2ispos = True
        try: # horrible hack #2
            p2 = eval_to_position(dim, topology, formula[2], variables, nodes)
            if p2 == None:
                ret = F
            if len(p2) != dim+1:
                raise Exception("Cannot compare value of cell, only node.")
        except KeyError:
            p2ispos = False
            p2val = variables[formula[2]] # we assume the keyerror is because this is symbol variable
        #all_vars.add(var_of_pos_expr(formula[2]))

        if not p1ispos and not p2ispos:
            if p1val == p2val:
                return T
            return F

        elif p1ispos and p2ispos:
            if ret == None:
                args = []
                for a in alphabet[1:]:
                    args.append(IFF(V(p1 + (a,)), V(p2 + (a,))))
                ret = AND(*args)

        else:
            if not p1ispos and p2ispos:
                p1, p2val = p2, p1val
            if p2val == alphabet[0]:
                ret = AND(*(NOT(V(p1 + (sym,))) for sym in alphabet[1:]))
            else:
                ret = V(p1 + (p2val,))
            
    elif op == "ISNEIGHBOR" or op == "ISPROPERNEIGHBOR":
        #print("test nbr")
        ret = None
        p1 = eval_to_position(dim, topology, formula[1], variables, nodes)
        if p1 == None:
            ret = F
        #print(formula[1], p1)
        all_vars.add(var_of_pos_expr(formula[1]))
        p2 = eval_to_position(dim, topology, formula[2], variables, nodes)
        if p2 == None:
            ret = F
        #print(formula[2], p2)
        all_vars.add(var_of_pos_expr(formula[2]))
        if ret == None:
            if op == "ISNEIGHBOR":
                nbhd = get_closed_nbhd(dim, topology, p1)
            else:
                nbhd = get_open_nbhd(dim, topology, p1)
            for n in nbhd: #get_closed_nbhd(dim, topology, p1):
                #print(n)
                if n == p2:
                    ret = T
                    break
            else:
                ret = F
        #print(ret)
    else:
        raise Exception("What " + op)
    #print ("from formula", formula)
    #print("ret", ret)
    return ret

def formula_to_circuit(nodes, dim, topology, alphabet, formula):
    assert len(alphabet) >= 2
    variables = {} 
    aux_var = [0] # da fuck is this?
    all_vars = set()
    form = formula_to_circuit_(nodes, dim, topology, alphabet, formula, variables, aux_var, all_vars)
    return tech_simp(form)

def collect_unbound_vars(formula, bound = None):
    #print("collecting", formula)
    if bound == None:
        bound = set()
    bound = set(bound)
    op = formula[0]
    #print(op, bound)
    possibles = set()
    if op == "BOOL":
        possibles.add(formula[1]) # a boolean variable's value is copied from enclosing
    elif op == "CIRCUIT":
        possibles.add(formula[1][0]) # same for circuit
        # but also collect in args
        args = formula[1][1:]
        for arg in args:
            possibles.update(collect_unbound_vars(arg, bound))
    elif op in ["CELLFORALL", "CELLEXISTSCELL", "NODEFORALL", "NODEEXISTS"]:
        var = formula[1]
        bound.add(var)
        for q in formula[2]: # collect vars used in bounds
            possibles.add(q)
        for q in collect_unbound_vars(formula[3], bound): # collect vars recursively in code
            possibles.add(q)
    elif op in ["FORALLVAL", "EXISTSVAL"]:
        valvar = formula[1]
        bound.add(valvar)
        rem_formula = formula[2]
        for q in collect_unbound_vars(rem_formula, bound): # collect vars recursively in code
            possibles.add(q)
    elif op in "TF":
        pass
    elif op in ["OR", "AND", "NOT", "IMP"]:
        args = formula[1:]
        for arg in args:
            possibles.update(collect_unbound_vars(arg, bound))
    # bool behaves like a circuit variable without variables; more efficient maybe since we just calculate a circuit
    elif op == "SETBOOL":
        var = formula[1]
        possibles.update(collect_unbound_vars(formula[2], bound)) # variable is not bound in the code to be binded
        bound.add(var)
        possibles.update(collect_unbound_vars(formula[3], bound)) # but is in evaluation of actual 
    # cvn[var] should be just the code, and a closure
    elif op == "SETCIRCUIT":
        var = formula[1][0]
        arg_names = formula[1][1:]
        circuit_code = formula[2]
        argbound = set(bound)
        argbound.update(arg_names)
        possibles.update(collect_unbound_vars(circuit_code, argbound))
        bound.add(var)
        possibles.update(collect_unbound_vars(formula[3], bound))
    elif op == "POSEQ" or op == "VALEQ":
        possibles.add(var_of_pos_expr(formula[1]))
        possibles.add(var_of_pos_expr(formula[2]))
    elif op == "HASVAL":
        possibles.add(var_of_pos_expr(formula[1]))
    elif op == "ISNEIGHBOR":
        possibles.add(var_of_pos_expr(formula[1]))
        possibles.add(var_of_pos_expr(formula[2]))
    else:
        raise Exception("What " + op)
    ret = set()
    for p in possibles:
        if p not in bound:
            ret.add(p)
    #print("now", ret)
    return ret

def var_of_pos_expr(f):
    while type(f) == list:
        f = f[0]
    return f

# a position expression is a list where
# we have first a position variable,
# then a bunch of edges. we will go forward along
# those edges
def eval_to_position(dim, topology, expr, pos_variables, nodes):
    #print("EVALTOPOS", expr, pos_variables)
    if type(expr) != list:
        #print("note list")
        #print("tking", pos_variables[expr])
        pos = pos_variables[expr]
        if type(pos) != tuple:
            #print("recu")
            return eval_to_position(dim, topology, pos, pos_variables, nodes)
        return pos
    pos = pos_variables[expr[0]]
    #print(pos, "ke")
    if type(pos) != tuple:
        pos = eval_to_position(dim, topology, pos, pos_variables, nodes)
    #print("ini", pos)
    for i in expr[1:]:
        #print(i)
        for t in topology:
            if len(t) == 3:
                a, b = t[1], t[2]
                if t[0] == i and (pos[dim] == None or pos[dim] == a[dim]):
                    #print("lauk")
                    if pos[dim] == None:
                        pos = vadd(vsub(pos[:-1], a[:-1]), b[:-1]) + (None,)
                    else:
                        pos = vadd(vsub(pos[:-1], a[:-1]), b[:-1]) + (a[dim],)
                    break
        else:
            if i in nodes: # single thing => change node
                pos = pos[:-1] + (i,)
            elif len(i) == dim and type(i) == tuple: # tuple of len dim => move
                pos = vadd(pos[:-1], i) + (pos[-1],)
            elif len(i) == dim+1 and type(i) == tuple: # tuple of len dim+1 => both
                pos = vadd(pos[:-1], i[:-1]) + (i[-1],)
        #print(pos)
    #print ("reton", pos)
    return pos

# given topology, positions of variables and bound dict
# list positions
def get_area(dim, topology, pos_variables, bound, typ, nodes):
    #print("getting area", bound)
    # for now, no bound means we're at the beginning
    if bound == {}:
        ret = set()
        ##print(typ)
        if typ == "NODE":
            for n in nodes:
                ret.add((0,)*dim + (n,))
        else:
            ret.add((0,)*dim + (None,))
        return ret
    area = set()
    for u in pos_variables:
        p = pos_variables[u]
        while type(p) != tuple:
            u = p
            p = pos_variables[u]
        #print(p, bound)
        if u not in bound:
            continue
        for t in get_ball(dim, topology, p, bound[u], nodes):
            if typ == "CELL":
                t = t[:-1] + (None,)
            area.add(t)
    #print(area)
    return area

def get_ball(dim, topology, pos, radius, nodes):
    # radius 0 of cell is special, and
    # probably the only sensible thing to do with cells
    if radius == 0 and pos[-1] == None:
        ret = set()
        for n in nodes:
            ret.add(pos[:-1] + (n,))
        return ret
    
    #print(pos, radius)
    frontier = set([pos])
    ball = set([pos])
    while radius > 0:
        radius -= 1
        newfrontier = set()
        for f in frontier:
            for n in get_nbhd(dim, topology, f):
                #print(n)
                if n in ball:
                    continue
                newfrontier.add(n)
                ball.add(n)
        frontier = newfrontier
    #print(ball)
    return ball

def get_open_nbhd(dim, topology, pos):
    ret = set()
    for t in topology:
        a, b = t[1], t[2]
        # if pos is a, then we add b
        if pos[dim] == None or t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret

def get_closed_nbhd(dim, topology, pos):
    ret = set()
    if pos[-1] != None:
        ret.add(pos)
    for t in topology:
        a, b = t[1], t[2]
        # if pos is a, then we add b
        if pos[dim] == None or t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret
        
def get_nbhd(dim, topology, pos):
    ret = set()
    for t in topology:
        a, b = t[1], t[2]
        # if pos is a, then we add b
        if pos[dim] == None or t[1][dim] == pos[dim]:
             v = vadd(vsub(pos[:-1], a[:-1]), b[:-1])
             ret.add(v + (b[-1],))
    return ret

"""
def vsub(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] - b[i])
    return tuple(c)

def vadd(a, b):
    c = []
    for i in range(len(a)):
        c.append(a[i] + b[i])
    return tuple(c)
"""

def start_cache(mini, maxi):
    #print("cahcae stat")
    circuit.Circuit.global_simplify = True
    circuit.Circuit.global_set = None
    #print(mini, maxi)
    circuit.Circuit.global_simplify_threshold_min = mini
    circuit.Circuit.global_simplify_threshold_max = maxi

def end_cache():
    #print("end ca")
    circuit.Circuit.global_simplify = False
    circuit.Circuit.global_set = None


"""
# golden mean shift
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

print(c)
"""

"""
assert str(c) == "C&(|(!(0, 0, 0), !(0, 1, 0)), |(!(0, 0, 0), !(0, -1, 0)), |(!(0, 0, 0), !(1, 0, 0)), |(!(0, 0, 0), !(-1, 0, 0)))"


# same with more letters
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       pos_variable_names = ["o", "v"],
                       circuit_variable_names = ["c"],
                       val_variable_names = [],
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1, 2],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                   ("SETCIRCUIT", "c", ("F",),
                                    ("OR", ("HASVAL", "o", 0),
                                    ("POSEQ", "o", "v"),
                                    ("HASVAL", "v", 0),
                                     ("CIRCUIT", "c"))))))

assert str(c) == "C&(|((0, 0, 0, 0), (0, 1, 0, 0)), |((0, 0, 0, 0), (0, -1, 0, 0)), |((0, 0, 0, 0), (1, 0, 0, 0)), |((0, 0, 0, 0), (-1, 0, 0, 0)))"


# one forces one up
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       pos_variable_names = ["o", "v"],
                       circuit_variable_names = ["c"],
                       val_variable_names = [],
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("NODEFORALL", "v", {"o" : 1},
                                    ("IMP", ("HASVAL", "o", 1),
                                     ("IMP", ("POSEQ", ["o", "up"], "v"),
                                      ("HASVAL", "v", 1))))))

assert str(c) == "C|(!(0, 0, 0), (0, 1, 0))"
"""

"""
# function test
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"),
                                   ("VALEQ", "u", "v"),
                                   ("CIRCUIT", ("c", "o", ["o", "up"])))))

assert str(c) == "C&(|(!(0, 0, 0), (0, 1, 0)), |(!(0, 1, 0), (0, 0, 0)))"
"""

"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("dn", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None, ('IMP', ('HASVAL', 'o', 1), ('HASVAL', ['o', 'dn'], 0))))

print(c)
"""

"""
# identifying code
c = formula_to_circuit(nodes = [0, 1], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,1)),
                                   ("dn", (0,0,1), (0,-1,0)),
                                   ("rt", (0,0,0), (0,0,1)),
                                   ("lt", (0,0,0), (-1,0,1)),
                                   ("rt", (0,0,1), (1,0,0)),
                                   ("lt", (0,0,1), (0,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"), # c = code word neighbor
                                   ("AND", ("HASVAL", "v", 1), ("ISNEIGHBOR", "u", "v")),
                                   ("AND", ("NODEEXISTS", "d", {"o": 1}, ("CIRCUIT", ("c", "o", "d"))),
                                    ("NODEFORALL", "p", {"o": 2},
                                     ("IMP", ("NOT", ("POSEQ", "p", "o")),
                                      ("NODEEXISTS", "q", {"o" : 1, "p" : 1},
                                       ("OR", ("AND", ("CIRCUIT", ("c", "o", "q")),
                                               ("NOT", ("CIRCUIT", ("c", "p", "q")))),
                                        ("AND", ("CIRCUIT", ("c", "p", "q")),
                                         ("NOT", ("CIRCUIT", ("c", "o", "q"))))))))))))
assert str(c) == "C&(&(|((0, 0, 0), (0, 0, 1), (-1, 0, 1), (0, 1, 1)), &(|((-1, 0, 0), (-1, -1, 0), (0, 0, 1), (0, 1, 1)), |((1, 2, 1), (-1, 0, 1), (1, 1, 0), (0, 0, 0), (0, 0, 1), (1, 1, 1)), |((0, 2, 1), (-1, 0, 1), (0, 1, 0), (-1, 1, 1), (0, 0, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 1), (0, 0, 0), (0, -1, 0), (-1, -1, 1), (0, 1, 1)), |((1, 0, 1), (-1, 0, 1), (0, 0, 0), (1, 0, 0), (1, 1, 1), (0, 1, 1)), |((-2, 0, 1), (-1, 1, 1), (0, 0, 0), (-1, 0, 0), (0, 0, 1), (0, 1, 1)), |((0, 0, 0), (-2, -1, 1), (-1, -1, 1), (-1, -1, 0), (0, 0, 1), (0, 1, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (0, 1, 1)), |((-1, 0, 1), (1, 1, 0), (0, 1, 0), (0, 0, 1)))), &(|((1, 0, 0), (0, 0, 0), (0, -1, 0), (0, 0, 1)), &(|((1, 0, 1), (0, 0, 0), (0, -1, 0), (2, 0, 0), (1, -1, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (-1, 0, 0), (-1, -1, 0), (0, 0, 1)), |((0, -1, 1), (0, 0, 0), (0, -2, 0), (1, 0, 0), (1, -1, 0), (0, 0, 1)), |((-1, 0, 1), (0, -1, 0), (1, 0, 0), (0, 1, 1)), |((0, -1, 1), (0, 0, 0), (-1, -1, 1), (1, 0, 0)), |((0, 0, 0), (-1, -1, 0), (-1, -1, 1), (1, 0, 0), (-1, -2, 0), (0, 0, 1)), |((1, 0, 1), (0, 0, 0), (0, -1, 0), (1, 1, 1)), |((1, 1, 0), (2, 1, 0), (0, 0, 0), (0, -1, 0), (0, 0, 1), (1, 1, 1)), |((1, 1, 0), (0, 1, 0), (0, -1, 0), (1, 0, 0), (0, 0, 1), (0, 1, 1)))))"

d = formula_to_circuit(nodes = [0, 1], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,1)),
                                   ("dn", (0,0,1), (0,-1,0)),
                                   ("rt", (0,0,0), (0,0,1)),
                                   ("lt", (0,0,0), (-1,0,1)),
                                   ("rt", (0,0,1), (1,0,0)),
                                   ("lt", (0,0,1), (0,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ("NODEFORALL", "o", {},
                                  ("SETCIRCUIT", ("c", "u", "v"), # c = code word neighbor
                                   ("AND", ("HASVAL", "v", 1), ("ISNEIGHBOR", "u", "v")),
                                   ("AND", ("NODEEXISTS", "d", {"o": 2}, ("CIRCUIT", ("c", "o", "d"))),
                                    ("NODEFORALL", "p", {"o": 3},
                                     ("IMP", ("NOT", ("POSEQ", "p", "o")),
                                      ("NODEEXISTS", "q", {"o" : 1, "p" : 1},
                                       ("OR", ("AND", ("CIRCUIT", ("c", "o", "q")),
                                               ("NOT", ("CIRCUIT", ("c", "p", "q")))),
                                        ("AND", ("CIRCUIT", ("c", "p", "q")),
                                         ("NOT", ("CIRCUIT", ("c", "o", "q"))))))))))))

"""

#for n in get_closed_nbhd(dim, topology, p1)
#variables {'u': ['o', 1], 'v': 'q', 'o': (0, 0, 0), 'q': (0, 0, 0)}
#from formula ('ISNEIGHBOR', 'u', 'v')
#ret CF()

"""

                       ("|", (":", ("var", 0), ("val", 0)), # either origin has value 0...
            ("@", ("var", 0), ("var", 1)),
            (":", ("var", 1), ("val", 0))) # or there is a neighbor w/ 0
           , [0, 1, 2])
"""

"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None,
                                  ('SETCIRCUIT', ('xor', 'a', 'b'),
                                   ('OR', ('AND', ('BOOL', 'a'), ('NOT', ('BOOL', 'b'))),
                                    ('AND', ('NOT', ('BOOL', 'a')), ('BOOL', 'b'))),
                                   ('CIRCUIT', ('xor', ('CIRCUIT', ('xor', ('HASVAL', 'o', 1),
                                                                    ('HASVAL', ['o', 'up'], 1))),
                                                ('HASVAL', ['o', 'dn'], 1))))))
print(c)
"""
"""
c = formula_to_circuit(nodes = [0], # N = nodes
                       dim = 2, # dimension
                       topology = [("up", (0,0,0), (0,1,0)),
                                   ("dn", (0,0,0), (0,-1,0)),
                                   ("rt", (0,0,0), (1,0,0)),
                                   ("lt", (0,0,0), (-1,0,0))], # topology
                       # quantifiers = [("A", "u", {}), ("A", "v", {"u" : 1})], # two quantifiers, Au: Ev(u1):
                       alphabet = [0, 1],
                       # Ao Av ||=o0=ov=v0
                       formula = ('NODEFORALL', 'o', None,
                                  ('SETCIRCUIT', ('xor', 'a', 'b'),
                                   ('OR', ('AND', ('BOOL', 'a'), ('NOT', ('BOOL', 'b'))),
                                    ('AND', ('NOT', ('BOOL', 'a')), ('BOOL', 'b'))),
                                   ('CIRCUIT', ('xor', ('HASVAL', 'o', 1), ('HASVAL', 'o', 1))))))
print(c)
"""



#("SET", ("c", "a"), ())

# quantification is like
# Av(u3 a4)  or
# Av7
# in this basic version, i.e. you can just say how far you look from u along the basic moves
