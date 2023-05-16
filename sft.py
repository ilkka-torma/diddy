from general import *
from circuit import *
from itertools import chain

# check that circuit is forced to be true when variable set
def forced_by(circuit, vals_as_list):
    andeds = []
    for (var, val) in vals_as_list:
        if val:
            andeds.append(V(var))
        else:
            andeds.append(NOT(V(var)))
    return models(andeds, circuit)

# we have a circuit and some values
# minimize the dict of values so that stays tautology
def minimize_solution(circuit, vals, necessary_vals = None):
    
    if necessary_vals == None:
        assert evaluate(circuit, vals)
        necessary_vals = []

    assert type(vals) == dict
    vals = list(vals.items())
    mini = minimize_solution_(circuit, vals, necessary_vals)
    as_dict = {}
    for (var, val) in mini:
        as_dict[var] = val
    return as_dict
        

def minimize_solution_(circuit, vals, necessary_vals):
    #print("juli", vals, necessary_vals)
    if len(vals) == 0:
        return necessary_vals

    first, rest = vals[0], vals[1:]
    if forced_by(circuit, rest + necessary_vals):
        return minimize_solution_(circuit, rest, necessary_vals)

    return minimize_solution_(circuit, rest, necessary_vals + [first])

# vecs is a list of vectors
def add_uniqueness_constraints(nodes, alphabet, circuits, vecs):
    if len(alphabet) == 2:
        return None
    #print("vecs", vecs)
    for vec in vecs:
        for node in nodes:
            pnvars = []
            for sym in alphabet[1:]:
                #print(alphabet)
                pnvars.append(V(vec + (node,sym)))
            #print("pnvars", pnvars)
            #print(list(map(str, pnvars)))
            #print(ATMOSTONE(*pnvars))
            circuits.append(ATMOSTONE(*pnvars))

def nonnegative_patterns(dim, tr_dims, patterns):
    "Translate the pattern to have nonnegative coodrinates along the specified dimensions"
    tr_vec = []
    for i in range(dim):
        if i in tr_dims:
            tr_vec.append(-min(vec[i] for vec in pat for pat in patterns))
        else:
            tr_vec.append(0)
    return [{nvadd(nvec, tr_vec) : val for (nvec, val) in pat.items()} for pat in patterns]

def nonnegative_circuit(dim, tr_dims, circ):
    circ = circ.copy()
    variables = circ.get_variables()
    tr_vec = []
    for i in range(dim):
        if i in tr_dims:
            tr_vec.append(-min(var[i] for var in variables))
        else:
            tr_vec.append(0)
    transform(circ, lambda var: vadd(var[:-2], tr_vec) + var[-2:])
    return circ

class SFT:
    "dim-dimensional SFT on a gridlike graph"

    # Onesided is a list of dimensions
    # In a onesided SFT, the set of forbidden patterns and the circuit are translated so that the onesided coordinates are nonnegative and start at 0
    def __init__(self, dim, nodes, alph, forbs=None, circuit=None, formula=None, onesided=None):
        self.dim = dim
        self.nodes = nodes
        self.alph = alph
        if onesided is None:
            onesided = []
        self.onesided = onesided

        if forbs is None:
            self.forbs = None
        else:
            self.forbs = nonnegative_patterns(self.dim, self.onesided, forbs)
        self.formula = formula # just for display, not actually used in computations
        if circuit is None:
            self.circuit = None
            self.deduce_circuit()
        else:
            self.circuit = nonnegative_circuit(self.dim, self.onesided, circuit)

    def __str__(self):
        return "SFT(dim={}, nodes={}, alph={}{})".format(self.dim, self.nodes, self.alph, (", onesided="+str(self.onesided)) if self.onesided else "")

    # Find recognizable configuration (i.e. uniformly eventually periodic in each orthogonal direction) in self which is not in other
    # The semilinear structure is a periodic rectangular tiling, and the contents of a rectangle depend on which axes its lowest corner lies
    # We could also have the sizes of the rectangles depend on this, but this is simpler for now
    # Some directions can be declared fully periodic instead of eventually periodic
    # For a onesided non-periodic direction, only consider translates of the formula whose variables are on the nonnegative part of the axis
    def exists_recognizable_not_in(self, other, radii, periodics=None, return_conf=False):
        #print("koko", self, other)

        if periodics is None:
            periodics = []
        
        my_vecs = set(var[:-2] for var in self.circuit.get_variables())
        other_vecs = set(var[:-2] for var in other.circuit.get_variables())
        conf_bounds = [(0 if i in self.onesided+periodics else -rad,
                        rad if i in periodics else 2*rad)
                       for (i, rad) in enumerate(radii)]
        all_positions = set(hyperrect(conf_bounds))
        tr_bounds = []
        for (i, rad) in enumerate(radii):
            if i in self.onesided+periodics:
                min_bound = 0
            else:
                min_bound = -rad - max(vec[i] for vec in chain(my_vecs, other_vecs))
            if i in periodics:
                max_bound = rad
            else:
                max_bound = 2*rad - min(vec[i] for vec in chain(my_vecs, other_vecs))
            tr_bounds.append((min_bound, max_bound))
        #print("radii", radii)
        #print("conf_bounds", conf_bounds)
        #print("tr_bounds", tr_bounds)

        def wrap(var):
            #print("var", var)
            ret = []
            for (i, (r,x)) in enumerate(zip(radii, var)):
                if i in periodics:
                    ret.append(x%r)
                elif x < 0:
                    ret.append(x%r - r)
                elif x < r:
                    ret.append(x)
                else:
                    ret.append(x%r + r)
            ret.extend(var[-2:])
            #print("ret", ret)
            return tuple(ret)

        circuits = []
        others = []
        for vec in hyperrect(tr_bounds):
            if any(vadd(vec, my_vec) in all_positions for my_vec in my_vecs) and\
               all(vec[i]+my_vec[i] >= 0 for my_vec in my_vecs for i in self.onesided):
                circ = self.circuit.copy()
                transform(circ, lambda var: wrap(nvadd(var[:-1], vec) + var[-1:]))
                circuits.append(circ)
            if any(vadd(vec, other_vec) in all_positions for other_vec in other_vecs) and\
               all(vec[i]+other_vec[i] >= 0 for other_vec in other_vecs for i in self.onesided) and\
               all(vec[i] == 0 or i not in periodics for i in range(self.dim)):
                not_other = NOT(other.circuit.copy())
                transform(not_other, lambda var: wrap(nvadd(var[:-1], vec) + var[-1:]))
                others.append(not_other)
        circuits.append(OR(*others))

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)

        m = SAT(AND(*circuits), True)
        
        if m == False:
            if return_conf:
                return False, None
            else:
                return False
        #print("model", m)
        if return_conf:
            conf = dict()
            for vec in hyperrect(conf_bounds):
                for node in self.nodes:
                    for sym in self.alph[1:]:
                        var = vec + (node, sym)
                        if m.get(var, False):
                            conf[vec + (node,)] = sym
                            break
                    else:
                        conf[vec + (node,)] = self.alph[0]
            return True, conf
        return True

    def ball_forces_allowed(self, other, r):
        all_positions = set()
        circuits = []

        bounds = [(0 if i in self.onesided else -r, r) for i in range(self.dim)]
        
        for vec in hyperrect(bounds):
            circ = self.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + var[-1:])
            for var in circ.get_variables():
                all_positions.add(var[:-2]) # drop node and letter
                #print(rel_pos)
            circuits.append(circ)

        not_other = NOT(other.circuit.copy())
        for var in not_other.get_variables():
            all_positions.add(var[:-2])
        circuits.append(not_other)

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)
        #print("no22")
        m = SAT(AND(*circuits))
        if m == False:
            return True
        return False

    def deduce(self, known_values, domain):
        #print(domain, known_values)
        #if len(self.alph) != 2:
        #    raise Exception("Only binary alphabets supported in deduce")
        
        circuits = {}
    
        for v in domain:
            circuits[v] = self.circuit.copy()
            for var in self.circuit.get_variables():
                # translate and add 0 at end so that we don't replace twice
                rel_pos = vadd(v, var[:-2]) + (var[-2], var[-1], 0) 
                substitute(circuits[v], var, V(rel_pos))
            #print(circuits[v])

        #print("that was circuits")
        forceds = set()
        for v in known_values:
            if known_values[v] == self.alph[0]:
                for a in self.alph[1:]:
                    forceds.add(NOT(V(v + (a, 0))))
                #forceds.add(V(v + (1, 0)))
            else:
                forceds.add(V(v + (known_values[v], 0)))
        #for f in forceds:
        #    print(f)
        #print("was forced")

        #print("no22")
        m = SAT(AND(*(list(circuits.values()) + list(forceds))), True)
        if m == False:
            print("nope")
            return None

        #print("limimisad", m)
        
        mm = {}
        for v in domain:
            for n in self.nodes:
                for a in self.alph[1:]:
                    if v + (n, a, 0) in m and m[v + (n, a, 0)]:
                        mm[v + (n,)] = a
                        break
                else:
                    mm[v + (n,)] = self.alph[0]
                """    
                    #print()
                    if m[v + (n, 1, 0)]:
                        mm[v + (n,)] = self.alph[1] #m[v + (n, 1, 0)]
                    else:
                        mm[v + (n,)] = self.alph[0]"""
                #else:
                #    print(v + (n, 1, 0), "not in")
                #    mm[v + (n,)] = None # was not actually discussed by rules
        #print("mmmm", mm)
        return mm

    # domain is a collection of nodevectors
    def all_patterns(self, domain, existing=None, extra_rad=0):

        if existing is None:
            existing = dict()
        
        vecs = set(vadd(nvec[:-1], tr)
                    for nvec in domain
                    for tr in centered_hypercube(self.dim, extra_rad))

        circuits = []
        all_positions = set()
        for vec in vecs:
            circ = self.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + var[-1:])
            for var in circ.get_variables():
                all_positions.add(var[:-2])
            circuits.append(circ)
            
        for (nvec, sym) in existing.items():
            if sym == self.alph[0]:
                circuits.extend(NOT(V(nvec+(a,))) for a in self.alph[1:])
            else:
                circuits.append(V(nvec+(sym,)))

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)

        for model in projections(AND(*circuits), [nvec+(sym,) for nvec in domain for sym in self.alph[1:]]):
            pat = dict()
            for nvec in domain:
                for sym in self.alph[1:]:
                    if model[nvec+(sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[0]
            yield pat
            
    # domain is a collection of nodevectors
    def all_periodic_points(self, dims, existing=None):
    
        if existing is None:
            existing = dict()
        
        domain = set([tuple()])
        for h in dims:
            domain = set(vec + (i,) for vec in domain for i in range(h))
        all_positions = domain
        domain = set(vec + (n,) for vec in domain for n in self.nodes)

        circuits = []
        for vec in domain:
            circ = self.circuit.copy()
            transform(circ, lambda var: nvmods(dims, nvadd(var[:-1], vec)) + var[-1:])
            circuits.append(circ)
            
        for (nvec, sym) in existing.items():
            if sym == self.alph[0]:
                circuits.extend(NOT(V(nvec+(a,))) for a in self.alph[1:])
            else:
                circuits.append(V(nvec+(sym,)))

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)

        for model in projections(AND(*circuits), [nvec+(sym,) for nvec in domain for sym in self.alph[1:]]):
            pat = dict()
            for nvec in domain:
                for sym in self.alph[1:]:
                    if model[nvec+(sym,)]:
                        pat[nvec] = sym
                        break
                else:
                    pat[nvec] = self.alph[0]
            yield pat

    def deduce_circuit(self):
        if self.circuit is None:
            anded = []
            for forb in self.forbs:
                ored = []
                for (nvec, c) in forb.items():
                    if c == self.alph[0]:
                        ored.extend(V(nvec+(d,)) for d in self.alph[1:])
                    else:
                        ored.append(NOT(V(nvec+(c,))))
                anded.append(OR(*ored))
            self.circuit = AND(*anded)

    def deduce_forbs(self, domain=None):
        self.forbs = []
        self.deduce_forbs_(domain)
        # deduce forbs gives the forbs with true/false variables,
        # we want to simplify them into an alphabet size independent form
        # self.clean_forbs()

    def clean_forbs(self):
        new_forbs = []
        for f in self.forbs:
            new_forb = {}
            for q in f:
                if len(self.alph) == 2:
                    if f[q]:
                        new_forb[q] = self.alph[1]
                    else:
                        new_forb[q] = self.alph[0]
                else:
                    if f[q]:
                        new_forb[q[:-1]] = q[-1]
            new_forbs.append(new_forb)
        self.forbs = new_forbs

    # domain is a list of vec+node+sym tuples
    def deduce_forbs_(self, domain=None):
        verbose_deb = True
        if type(domain) == int:
            domain = [vec + (node, a) for vec in centered_hypercube(self.dim, domain)
                      for node in self.nodes for a in self.alph[1:]]
        if domain is None:
            domain = list(self.circuit.get_variables())
        vec_domain = set(var[:-2] for var in domain)
        #print("nvec_domain", vec_domain)
        #assert len(self.alph) == 2
        assert all(v in domain for v in self.circuit.get_variables())

        # we want to tile domain so that it has no existing forbos, but
        # the circuit fails at the origin
        complemented = NOT(self.circuit.copy())
        #print("complemented", complemented)
        forbiddens = []
        for forb in self.forbs:
            #print("implementing forb", forb)
            # anchor is just some position in domain of forbo (without node info)
            # which we will position in various places
            anchor = list(forb)[0][:-1]
            for vec in vec_domain:
                for forb_vec in forb:
                    #print("testing vec", nvadd(nvsub(forb_vec, anchor), vec))
                    if vadd(vsub(forb_vec[1:], anchor), vec) not in vec_domain:
                        #print("nope")
                        break
                # we go here if the entire forbidden pattern translate fits in domain
                else:
                    #print("here")
                    # we make a circuit that says that we differ from the pattern somewhere
                    oreds = []
                    for (forb_vec, value) in forb.items():
                        local_vec = nvadd(nvsub(forb_vec, anchor), vec)
                        if value == self.alph[0]:
                            oreds.extend(V(local_vec+(sym,)) for sym in self.alph[1:])
                        else:
                            oreds.append(NOT(V(local_vec+(value,))))
                    forbiddens.append(OR(*oreds))

        #print("formulas", forbiddens)
        add_uniqueness_constraints(self.nodes, self.alph, forbiddens, vec_domain)
        #print("uniq formulas", forbiddens)

        m = SAT(AND(complemented, *forbiddens), True)
        if m == False:
            return None

        # we now know that m is a forbidden thingy
        # we then try to minimize it...
        minimal = {}
        for v in complemented.get_variables():
            minimal[v] = m[v]
        #print("minimizing", minimal)
        minimal = minimize_solution(complemented, minimal)
        #a = bbb
        #print("got", minimal)
        new_forb = dict()
        for (nvec_sym, val) in minimal.items():
            if val:
                new_forb[nvec_sym[:-1]] = nvec_sym[-1]
            else:
                new_forb[nvec_sym[:-1]] = self.alph[0]

        #print("new forb", new_forb)
        if verbose_deb and False: # todo
            assert len(self.alph) == 2
            forb_str = ""
            for t in sorted(minimal):
                 print(t, minimal[t])
            

        self.forbs.append(new_forb)
        
        self.deduce_forbs_(domain)

    def contains(self, other, limit = None, return_radius_and_sep = False, method="periodic"):
        "Test containment using forced allowed patterns or special configurations"
        r = 1
        while limit is None or r <= limit:
            if other.ball_forces_allowed(self, r):
                if return_radius_and_sep:
                    return True, r, None
                return True
            if method == "recognizable":
                res, sep = other.exists_recognizable_not_in(self, [r]*self.dim, return_conf=return_radius_and_sep)
            elif method == "periodic":
                res, sep = other.exists_recognizable_not_in(self, [r]*self.dim, periodics = [i for i in range(self.dim) if i not in self.onesided], return_conf=return_radius_and_sep)
            else:
                raise Exception("Unknown method: {}".format(method))
            if res:
                if return_radius_and_sep:
                    return False, r, sep
                return False
            r += 1
        return None

    def equals(self, other, limit = None, return_radius = False, method=None):
        c12, rad, _ = self.contains(other, limit, return_radius_and_sep = True, method="periodic")
        if c12 == None:
            return None, limit
        elif c12 == False:
            return False, rad
        c21, rad2, _ = other.contains(self, limit, return_radius_and_sep = True, method=method)
        if c21 == None:
            return None, limit
        return c21, max(rad, rad2)

    def all_patterns_splitting(self, domain, known_values=None, extra_rad=0, rec=0):
        "Compute the number of patterns on given domain"
        if known_values is None:
            known_values = dict()

        variables = set(self.circuit.get_variables())
        var_dims = []
        dom_dims = []
        for i in range(self.dim):
            vdmin, vdmax = min(var[i] for var in variables), max(var[i] for var in variables)
            if vdmin == vdmax:
                vdmax += 1
            var_dims.append((vdmin, vdmax))
            dom_dims.append((min(nvec[i] for nvec in domain), max(nvec[i] for nvec in domain)))

        diff, splitdim = max((max_dd-min_dd-max_vd+min_vd-1, i) for (i, ((min_vd, max_vd), (min_dd, max_dd))) in enumerate(zip(var_dims, dom_dims)))
        if diff >= 3:
            # recurse
            min_vd, max_vd = var_dims[splitdim]
            min_dd, max_dd = dom_dims[splitdim]
            mid_pos = (min_dd+max_dd+min_vd-max_vd+1)//2
            #mid_vec = (0,)*splitdim + ((mid_pos,) + (0,)*(self.dim-splitdim-1)
            mid_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim] < mid_pos+max_vd-min_vd)
            left_domain = set(nvec for nvec in domain if nvec[splitdim] < mid_pos+max_vd-min_vd)
            right_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim])
            for mid_pat in self.all_patterns_splitting(mid_domain, known_values=known_values, extra_rad=extra_rad, rec=rec+1):
                mid_pat.update(known_values)
                rpats = list(self.all_patterns_splitting(right_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1))
                for lpat in self.all_patterns_splitting(left_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1):
                    for rpat in rpats:
                        newpat = rpat.copy()
                        rpat.update(lpat)
                        yield newpat
        else:
            # compute by brute force
            for pat in self.all_patterns(domain, existing=known_values, extra_rad=extra_rad):
                yield pat
                   
    def count_patterns_splitting(self, domain, known_values=None, extra_rad=0, rec=0):
        "Compute the number of patterns on given domain"
        if known_values is None:
            known_values = dict()

        variables = set(self.circuit.get_variables())
        var_dims = []
        dom_dims = []
        for i in range(self.dim):
            vdmin, vdmax = min(var[i] for var in variables), max(var[i] for var in variables)
            if vdmin == vdmax:
                vdmax += 1
            var_dims.append((vdmin, vdmax))
            dom_dims.append((min(nvec[i] for nvec in domain), max(nvec[i] for nvec in domain)))

        diff, splitdim = max((max_dd-min_dd-max_vd+min_vd-1, i) for (i, ((min_vd, max_vd), (min_dd, max_dd))) in enumerate(zip(var_dims, dom_dims)))
        if diff >= 3:
            # recurse
            min_vd, max_vd = var_dims[splitdim]
            min_dd, max_dd = dom_dims[splitdim]
            mid_pos = (min_dd+max_dd+min_vd-max_vd+1)//2
            #mid_vec = (0,)*splitdim + ((mid_pos,) + (0,)*(self.dim-splitdim-1)
            mid_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim] < mid_pos+max_vd-min_vd)
            left_domain = set(nvec for nvec in domain if nvec[splitdim] < mid_pos+max_vd-min_vd)
            right_domain = set(nvec for nvec in domain if mid_pos <= nvec[splitdim])
            summa = 0
            for mid_pat in self.all_patterns_splitting(mid_domain, known_values=known_values, extra_rad=extra_rad, rec=rec+1):
                mid_pat.update(known_values)
                lefts = self.count_patterns_splitting(left_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1)
                rights = self.count_patterns_splitting(right_domain, known_values=mid_pat, extra_rad=extra_rad, rec=rec+1)
                summa += lefts*rights
            return summa
        else:
            # compute by brute force
            return sum(1 for _ in sealf.all_patterns(domain, existing=known_values, extra_rad=extra_rad))

    def keep_tiling(self):
        r = 1
        while True:
            print(r)

            m = self.tile_box(r)
            assert m
            
            r += 1
        return None

    def tile_box(self, r):
        all_positions = set()
        circuits = []
        
        for vec in centered_hypercube(self.dim, r):
            circ = self.circuit.copy()
            transform(circ, lambda var: nvadd(var[:-1], vec) + var[-1:])
            for var in circ.get_variables():
                all_positions.add(var[:-2]) # drop node and letter
            circuits.append(circ)

        add_uniqueness_constraints(self.nodes, self.alph, circuits, all_positions)

        m = SAT(AND(*circuits))
        return not (m == False)

            
