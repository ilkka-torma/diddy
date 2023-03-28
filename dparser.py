"""
parse takes a string which represents a full program
in our language, and parses the entire program

token means string or integers or whatever
name is a string
"""

import fractions

alphabet = [0, 1]
accept_repeats_in_forbos = True
parse_default = False

def parse(s):
    commands =[]
    while s != "":
        command, s = parse_command(s)
        if command == None:
            return commands
        if command == True:
            continue
        commands.append(command)
    return commands

"""
arguments are: name, alternate names, list_command, initial_args
list_command = True means we expect a ;-separated list of argument lists
list_command = False means we read a list of arguments
if list_command = True, then initial_args is how many
arguments we read before going into the first list
"""
basic_commands = [("Wang", ["wang"], True, 1)]

def parse_command(s):
    #print("parsin", s[:20], "---")
    _, s = ignore_space(s)
    if len(s) == 0 or s.isspace():
        return None, s
    """
    if s[:2] == "--":
        _, s = parse_comment(s)
        return True, s
    """
    
    #assert len(s) > 0 and s[0] == "%"
    if len(s) == 0 or s[0] != "%":
        raise Exception("Parsing failed near %s." % s[:20])
    
    op, s = read_word(s[1:])
    if op == "nodes":
        l, s = read_simple_token_list(s)
        return ("nodes", l), s
    elif op == "dim":
        l, s = read_number(s)
        return ("dim", l), s
    elif op == "topology":
        l, s = read_any_symbol(s, ["squaregrid", "square", "grid", "hexgrid", "hex", "king", "kinggrid", "triangle", "trianglegrid"])
        if l != None:
            return ("topology", l), s
        simplices = []
        while True:
            #print("kime")
            simplex, s = read_simplex(s)
            if simplex != None:
                simplices.append(simplex)
                _, s = ignore_space(s)
                _, s = ignore_symbol(s, ";")
                _, s = ignore_space(s)
            else:
                break
        return ("topology", simplices), s
    elif op == "alphabet":
        l, s = read_simple_token_list(s)
        global alphabet
        alphabet = l
        return ("alphabet", l), s
    # clopens and SFTs are internally represented the same way (first variable is be forall-quantified)
    # except we tag with the type
    elif op in ["set", "SFT", "clopen"]:
        name, s = read_name(s, True)
        #print(name, "kim")
        _, s = ignore_space(s)
        
        # set is defined by a formula
        if s[0] in "AEO":            
            formula, s = read_formula(s)
            if op == "SFT":
                if formula[0] not in ["NODEFORALL", "CELLFORALL"]:
                    raise Exception("When defining SFT, first quantifier must be A.")
            elif op == "clopen":
                if formula[0] not in ["NODEORIGIN", "CELLORIGIN"]:
                    raise Exception("When defining SFT, first quantifier must be O.")
            else:
                if formula[0] in ["NODEFORALL", "CELLFORALL"]:
                    op = "SFT"
                else:
                    op = "clopen"
            formula = (formula[0][:4] + "FORALL",) + formula[1:]
            return (op, name, "formula", formula), s
        
        # set is defined by forbidden patterns
        if s[0] == "(":
            if op not in ["SFT", "clopen"]:
                raise Exception("When giving explicit forbidden patterns, use SFT or clopen command.")
            forbos, s = read_forbidden_patterns(s)
            return (op, name, "forbos", forbos), s

    elif op == "set_weights":
        weights = {}
        while True:
            symbol, s = read_simple_token(s)
            if symbol == None:
                break
            weight, s = read_fraction(s)
            weights[symbol] = weight
        return (op, weights), s
            
    elif op == "minimum_density":
        name, s = read_name(s, True)
        periods = []
        while True:
            period, s = read_vector(s)
            if period != None:
                periods.append(period)
            else:
                break
        return ("minimum_density", name, periods), s

    elif op in ["show_formula", "show_forbidden_patterns", "show_parsed"]:
        name, s = read_name(s, True)
        return (op, name), s

    elif op == "compute_forbidden_patterns":
        name, s = read_name(s, True)
        rad, s = read_number(s)
        return (op, name, rad), s

    elif op[:5] == "equal" or op[:8] == "contains":
        name, s = read_name(s, True)
        name2, s = read_name(s, True)
        return (op, name, name2), s

    elif op == "compare_SFT_pairs" or op == "compare_SFT_pairs_equality":
        return (op,), s
    
    else:
        args = []
        """
        some commands expect a list of argument lists separated by semicolon,
        and we should set list_command = True so that they work correctly for
        a single list without the semicolon; None means we don't know
        """
        arglists = []
        list_command = None
        """
        some of the commands (%Wang) expecting a list have a name and _then_ the list
        of argument, and we set initial_args = 1; some commands (%topology) just
        have a list of argument lists
        """
        initial_args = 0

        parse_as_default = True
        
        # cmd = e.g. ("Wang", ["wang"], True, 1)
        for cmd in basic_commands:
            name, alts, lc, ia = cmd
            if name == op or op in alts:
                parse_as_default = False
                list_command = lc
                initial_args = ia
                break
            #print(name, op)
        
        if parse_as_default and not parse_default:
            raise Exception("Bad command %s near: " % op + s[:30])

        # this allows us to try to keep parsing after a semicolon,
        # but we can raise an exception if we actually manage to parse
        # something; the point is we don't punish for a semicolon after
        # a command
        must_be_done = False

        kwargs = {}
        flags = {}
        while True: # this parses list of argument lists
            if len(args) > 0:
                must_be_done = True
            while True: # this parses a single argument list
                #print("largs", repr(s))
                kwarg, s = read_keyword_arg(s)
                #print(kwarg)
                if kwarg != None:
                    #args.append(kwarg)
                    assert kwarg[0] == "KWARG"
                    #if len(arglists) != 0:
                    #    raise Exception("Keyword arguments not allowed in list of argument lists.")

                    # it turns out that it's nice to allow "keyword args" also in list,
                    # namely in Wang tiles...
                    # but then we won't put them on the kwargs list but return a SET-tuple...

                    if len(arglists) == 0 and len(args) <= initial_args:
                        kwargs[kwarg[1]] = kwarg[2]
                    else:
                        if must_be_done:
                            raise Exception("%s wants a simple argument list, but is given a list of lists." % op)
                        args.append(("SET", kwarg[1], kwarg[2]))
                    continue
                    #print(kwarg)
                flag, s = read_flag(s)
                if flag != None:
                    assert flag[0] == "FLAG"
                    if len(arglists) != 0:
                        raise Exception("Flags not allowed in list of argument lists.")
                    flags[flag[2]] = flag[1]
                else:
                    arg, s = read_object(s)
                    if arg == None:
                        break
                    #print(repr(arg))
                    if must_be_done: #list_command == False and len(arglists) > 0:
                        raise Exception("%s wants a simple argument list, but is given a list of lists." % op)
                    args.append(arg)
            _, s = ignore_space(s)
            if len(args) != 0 and (s[:1] == ";" or list_command == True) and (list_command != False):
                #print("klu")
                list_command = True
                if len(arglists) == 0:
                    initials = args[:initial_args]
                    args = args[initial_args:]
                if len(args) > 0: # if name is followed by ; we do not punish
                    arglists.append(args)
                args = []
            #print(list_command, args, arglists)
            #if list_command == False and len(args) != 0 and len(arglists) != 0:
            #    raise Exception("%s wants a simple argument list." % op)

            sym, s = ignore_symbol(s, ";")
            if sym == None: # or list_command == False:
                break
            
        if list_command == True:
            #print("mois")
            #if first_is_name:
            return (op,) + tuple(initials) + (arglists, kwargs, flags), s
            #print(arglists)
            # return (op, arglists), s
        #print("her")
        return (op, args, kwargs, flags), s
    
# ignore space, including comments
def ignore_space(s):
    #print("Space", s[:20])
    i = 0
    while i < len(s):
        if not s[i].isspace():
            if s[i:i+2] == "--":
                _, s = ignore_until_eol(s[i:])
                i = 0
                continue
            return None, s[i:]
        i += 1
    return None, ""

def ignore_until_eol(s):
    assert s[:2] == "--"
    idx = s.find("\n")
    if idx == -1:
        return None, ""
    return None, s[idx+1:]

# ignore space, including comments, but not eol
def ignore_space_except_eol(s):
    i = 0
    while i < len(s):
        if s[i] == "\n":
            return None, s[i:]
        elif not s[i].isspace():
            if s[i:i+2] == "--":
                return ignore_until_eol_except_eol(s[i:])
            return None, s[i:]
        i += 1
    return None, ""

def ignore_until_eol_except_eol(s):
    assert s[:2] == "--"
    idx = s.find("\n")
    if idx == -1:
        return None, ""
    return None, s[idx:]

def read_word(s, allow_digits = False):
    #print("word", s[:20])
    _, ss = ignore_space(s)
    i = 0
    while i < len(ss):
        if allow_digits:
            break_condition = not ss[i].isalpha() and ss[i] != "_" and not ss[i].isdigit()
        else:
            break_condition = not ss[i].isalpha() and ss[i] != "_"
        if break_condition:
            if i > 0 and not ss[:i].isdigit():
                return ss[:i], ss[i:]
            return None, s
        i += 1
    if len(ss) > 0:
        return ss, ""
    return None, s

# names in the command language allow combining numbers and letters
def read_high_level_name(s):
    return read_word(s, True)

# names in the formula language are alpha only, so we just parse a word
def read_name(s, allow_digits = False):
    return read_word(s, allow_digits)

def read_number(s):
    _, s = ignore_space(s)
    i = 0
    while i < len(s):
        if not s[i].isdigit():
            if i > 0:
                return int(s[:i]), s[i:]
            return None, s
        i += 1
    if len(s) > 0:
        return int(s), ""
    return None, s

def read_keyword_arg(s):
    _, ss = ignore_space(s)
    name, ss = read_name(ss)
    if name == None:
        return None, s
    _, ss = ignore_space(ss)
    sym, ss = read_symbol(ss, "=")
    if sym == None:
        return None, s
    val, ss = read_object(ss)
    if val == None:
        return None, s
    return ("KWARG", name, val), ss

# read object for command language
def read_object(s):
    _, ss = ignore_space(s)
    ret, ss = read_list(ss)
    if ret != None:
        return ret, ss
    ret, ss = read_vector(ss)
    if ret != None:
        #print("vector", ret)
        return ret, ss
    ret, ss = read_signed_number(ss)
    if ret != None:
        #print("signed num", ret)
        return ret, ss
    ret, ss = read_fraction(ss)
    if ret != None:
        #print("fraction", ret)
        return ret, ss
    ret, ss = read_number(ss)
    if ret != None:
        #print("num", ret)
        return ret, ss
    ret, ss = read_high_level_name(ss)
    if ret != None:
        #print("name", ret)
        return ret, ss
    return None, s

# this is more or less the same as a vector, but reads general objects
def read_list(s):
    _, ss = ignore_space(s)
    if ss[:1] == "[":
        ss = ss[1:]
    else:
        return None, s
    vec = []
    _, ss = ignore_space(ss)
    while True:
        entry, ss = read_object(ss)
        if entry == None:
            break
        vec.append(entry)
        _, ss = ignore_space(ss)
        _, ss = ignore_symbol(ss, ",") # it's fine to separate by comma
        _, ss = ignore_space(ss)
        # raise Exception("Unexpected token while reading list:", s[0])
    _, ss = ignore_space(ss)
    if ss[:1] != "]":
        return None, s
    return vec, ss[1:]

def read_flag(s):
    _, ss = ignore_space(s)
    sym, ss = read_symbol(ss, "@")
    if sym == None and ss[:1] != "!":
        return None, s

    # we either read a sign or ! which means negation and only used for flags...
    sign = True
    while ss[:1] == "!":
        sign = not sign
    obj, ss = read_object(ss)
    if obj == None:
        return None, s
    return ("FLAG", sign, obj), ss

def read_signed_number(s):
    _, s = ignore_space(s)
    sign = 1
    while s[:1] == "-":
        sign *= -1
        s = s[1:]
        _, s = ignore_space(s)
    i = 0
    while i < len(s):
        if not s[i].isdigit():
            if i > 0:
                #print("reht")
                return int(s[:i]) * sign, s[i:]
            #print("veli2")
            return None, s
        i += 1
    if len(s) > 0:
        return int(s) * sign, ""
    return None, s

def read_fraction(s):
    _, ss = ignore_space(s)
    sign = 1
    while ss[:1] == "-":
        sign *= -1
        ss = ss[1:]
        _, ss = ignore_space(ss)
    i = 0
    numerator = ""
    while i < len(ss):
        if not ss[i].isdigit():
            if i > 0:
                numerator = int(ss[:i]) * sign
                break
            else:
                return None, s
        i += 1
    if ss[i:i+1] != "/":
        return None, s
    ss = ss[i+1:]
    denominator = ""
    while i <= len(ss):
        if i == len(ss) or not ss[i].isdigit():
            if i > 0:
                denominator = int(ss[:i])
                break
            else:
                return None, s
        i += 1
            
    return fractions.Fraction(numerator, denominator), ss[i:]

def read_vector(s):
    _, s = ignore_space(s)
    if s and s[0] == "(":
        s = s[1:]
    else:
        return None, s
    vec = []
    _, s = ignore_space(s)
    while True:
        entry, s = read_signed_number(s)
        vec.append(entry)
        _, s = ignore_space(s)
        if s[0] == ",":
            _, s = ignore_space(s[1:])
            continue
        elif s[0] == ")":
            s = s[1:]
            break
        else:
            raise Exception("Unexpected token while reading vector:", s[0])
    return tuple(vec), s

def read_forbidden_patterns(s):
    _, s = ignore_space(s)
    forbos = []
    while True:
        forbo, s = read_forbidden_pattern(s)
        if forbo == None:
            return forbos, s
        #print("forbo", forbo)
        forbos.append(forbo)
        _, s = ignore_space(s)
        _, s = ignore_symbol(s, ";")
        _, s = ignore_space(s)
    return forbos, s

def read_forbidden_pattern(s):
    # print("asdfsa", s[:20])
    _, s = ignore_space(s)
    pattern = {}
    while True:
        vector, s = read_vector_for_simplex(s)
        if vector == None:
            #print("breaing")
            break
        #print(vector)
        _, s = ignore_space_except_eol(s)
        _, s = ignore_symbols(s, ["=", "->", ":"])
        _, s = ignore_space_except_eol(s)
        value, s = read_simple_token(s)
        #print(value, "lkois")
        vector = tuple(vector)
        if not accept_repeats_in_forbos:
            assert vector not in pattern
        pattern[vector] = value
        _, s = ignore_space_except_eol(s)
        _, s = ignore_symbol(s, ",")
        _, s = ignore_space_except_eol(s)
    if len(pattern) == 0:
        return None, s
    # remove the variables
    fixed_pattern = {}
    varnames = None
    for vec in pattern:
        if varnames == None:
            varnames = []
            for i,t in enumerate(vec[:-1]):
                varnames.append(t[0]) # for checking that all have same variable name
        for i,t in enumerate(vec[:-1]):
            assert t[0] == varnames[i] # check that is same as in first
        assert vec[-1][0] == None # no varname in node
        fixed_vec = tuple([i[1] for i in vec])
        assert fixed_vec not in fixed_pattern
        fixed_pattern[fixed_vec] = pattern[vec]
    return fixed_pattern, s

def read_simplex(s):
    #print("simp", s[:20])
    _, s = ignore_space(s)
    name, s = read_word(s)
    #print(name, s[:15], "vili")
    if name == None:
        return None, s
    #print(name, s[:29], "----")
    vectors = []
    while True:
        vector, s = read_vector_for_simplex(s)
        #print(vector, s)
        if vector == None:
            break
        vectors.append(vector)
    if len(vectors) != 2:
        raise Exception("Only edges supported in topology.")
    a, b = vectors[0], vectors[1]
    #print("ki", a, b)
    assert len(a) == len(b)
    aa, bb = [], []
    for i in range(len(a) - 1):
        assert a[i][0] == b[i][0] # variables the same
        aa.append(a[i][1])
        bb.append(b[i][1])
    v = vsub(bb, aa)
    #assert a[-1][0] == b[-1][0] == None # no variable in node
    if a[-1][0] != None:
        lasta = a[-1][0]
    else:
        lasta = a[-1][1]
    if b[-1][0] != None:
        lastb = b[-1][0]
    else:
        lastb = b[-1][1]
    return (name, (0,)*(len(a)-1) + (lasta,), v + (lastb,)), s
    
def read_vector_for_simplex(s):
    #print("vect", s[:20])
    _, ss = ignore_space(s)
    if ss[:1] == "(":
        #print("je")
        ss = ss[1:]
        vector = []
        while True:
            #print("Ki", ss[:15])
            var_plus_num, ss = read_var_plus_num(ss)
            #print("ext",var_plus_num)
            _, ss = ignore_space(ss)
            _, ss = ignore_symbol(ss, ",")
            _, ss = ignore_space(ss)
            if var_plus_num == None:
                break
            vector.append(var_plus_num)
            #print(var_plus_num)
        if len(vector) > 0:
            #print("elem", vector, ss)
            assert ss[:1] == ")"
            return vector, ss[1:]
    return None, s

def ignore_symbols(s, syms):
    for sym in syms:
        sym_gotten, s = ignore_symbol(s, sym)
        if sym_gotten != None:
            return sym_gotten, s
    return None, s

def ignore_symbol(s, sym):
    if len(s) > 0 and s[0] == sym:
        return s[0], s[1:]
    return None, s

def read_symbol(s, sym):
    _, ss = ignore_space(s)
    if ss[:len(sym)] == sym:
        return sym, ss[len(sym):]
    return None, s

def read_any_symbol(s, syms):
    for sym in syms:
        l, s = read_symbol(s, sym)
        if l != None:
            return l, s
    return None, s

def read_var_plus_num(s):
    ss = s
    #print("vpm", s[:20])
    # try to read just a number
    _, ss = ignore_space(ss)
    num, ss = read_signed_number(ss)
    #print(num, s)
    if num == None:
        #print("rve")
        name, ss = read_name(ss)
        #print("name")
        if name == None:
            return None, s
        _, ss = ignore_space(ss)
        _, ss = ignore_symbol(ss, "+")
        _, ss = ignore_space(ss)
        num, ss = read_signed_number(ss)
        if num == None:
            num = 0
        return (name, num), ss
    return (None, num), ss    

def read_simple_token_list(s):
    #print("stl", s[:20])
    tokens = []
    while True:
        #print(s)
        token, s = read_simple_token(s)
        #print(s)
        if token != None:
            tokens.append(token)
        else:
            return tokens, s

# things like v.up.dn but ALSO numbers
def read_dotted_token_list(s):
    _, s = ignore_space(s)
    word, s = read_word(s)
    if word == None:
        num, s = read_number(s)
        if num == None:
            return None, s
        return num, s
    words = [word]
    while True:
        #_, s = ignore_space(s)
        if s[:1] != ".":
            if len(words) == 1:
                return words[0], s
            return words, s
        s = s[1:]
        word, s = read_simple_token(s) # these can be numbers, since nodes can be numbers
        words.append(word)

#print(read_dotted_token_list("o.up"))
#a = bb

def read_simple_token(s):
    #print("sim tok", s[:20])
    _, s = ignore_space(s)
    word, s = read_word(s)
    if word == None:
        num, s = read_number(s)
        if num == None:
            return None, s
        return num, s
    return word, s





def vsub(a, b):
    r = []
    for i in range(len(a)):
        r.append(a[i] - b[i])
    return tuple(r)

def read_bound(s):
    ss = s
    _, ss = ignore_space(ss)
    #print("read bouind", ss[:20])
    if ss[0] == "[":
        bounds = {}
        ss = ss[1:]
        while True:
            _, ss = ignore_space(ss)
            name, ss = read_name(ss)
            _, ss = ignore_space(ss)
            num, ss = read_number(ss)
            if name == None or num == None:
                break
            bounds[name] = num
        _, ss = ignore_space(ss)
        assert ss[0] == "]"
        ss = ss[1:]
        return bounds, ss
    return None, s

def read_let(s):
    ss = s
    _, ss = ignore_space(ss)
    # circ, ss = read_name(ss)
    call = []
    while True:
        _, ss = ignore_space(ss)
        name, ss = read_name(ss)
        if name != None:
            call.append(name)
        else:
            break
    _, ss = ignore_space(ss)
    assert ss[:2] == ":="
    assert len(call) > 0
    ss = ss[2:]
    expr, ss = read_formula(ss)
    _, ss = ignore_space(ss)
    if ss[:2] != "in":
        raise Exception("Excepted 'in' at " + ss[:30])
    expr2, ss = read_formula(ss[2:])
    return ("SETCIRCUIT", tuple(call), expr, expr2), ss

def read_formula(s):
    #print("readig form", s)
    ss = s
    _, ss = ignore_space(ss)
    if len(ss) == 0:
        raise Exception("Excepted formula at '" + ss[:30] + "...'")
    if ss[0] in "AEO":
        quant = {"A" : "FORALL", "E" : "EXISTS", "O" : "ORIGIN"}[ss[0]]
        typ = "NODE"
        if ss[1] == "C":
            typ = "CELL"
            ss = ss[2:]
        else:
            ss = ss[1:]
        var, ss = read_name(ss)
        _, ss = ignore_space(ss)
        bound, ss = read_bound(ss)
        formula, ss = read_formula(ss)
        return (typ+quant, var, bound, formula), ss
    elif ss[:3] == "let":
        return read_let(ss[3:])
    else: #ss[:3] == "let":
        expr, ss = read_basic_expression(ss)
        return expr, ss
    raise Exception("Exception: Cannot parse formula at " + ss[:30])

# read a bunch of <->'s, since that's the top level op type
# then read a bunch of ->'s
# then read a bunch of |'s
# then &'s
# at bottom we have @v = a, u ~ v, u = v, @u = @v
def read_basic_expression(s):
    #print("reading basic", s[:20])
    ss = s
    imps = []
    while True:
        #print("eq iter", ss[:20])
        imp, ss = read_imp_expression(ss)
        if imp != None:
            imps.append(imp)
        else:
            break
        _, ss = ignore_space(ss)
        if ss[:3] != "<->":
            break
        ss = ss[3:]
        
    if len(imps) == 0:
        return None, s
    elif len(imps) == 1:
        return imps[0], ss
    else:
        return ("IFF", *imps), ss

def read_imp_expression(s):
    #print("reading imp", s[:20])
    ss = s
    ors = []
    while True:
        #print("imp iter", ss[:20])
        or_, ss = read_and_expression(ss)
        if or_ != None:
            ors.append(or_)
        else:
            break
        _, ss = ignore_space(ss)
        if ss[:2] != "->":
            break
        ss = ss[2:]
    if len(ors) == 0:
        return None, s
    elif len(ors) == 1:
        return ors[0], ss
    else:
        return ("IMP", *ors), ss

def read_and_expression(s):
    #print("reading or", s[:20])
    ss = s
    ors = []
    while True:
        or_, ss = read_or_expression(ss)
        if or_ != None:
            ors.append(or_)
        else:
            break
        _, ss = ignore_space(ss)
        if ss[:1] != "&":
            break
        ss = ss[1:]
    if len(ors) == 0:
        return None, s
    elif len(ors) == 1:
        return ors[0], ss
    else:
        return ("AND", *ors), ss

def read_or_expression(s):
    #print("reading or", s[:20])
    ss = s
    nots = []
    while True:
        not_, ss = read_not_expression(ss)
        if not_ != None:
            nots.append(not_)
        else:
            break
        _, ss = ignore_space(ss)
        if ss[:1] != "|":
            break
        ss = ss[1:]
    if len(nots) == 0:
        return None, s
    elif len(nots) == 1:
        return nots[0], ss
    else:
        return ("OR", *nots), ss

def read_not_expression(s):
    #print("reading not", s[:20])
    ss = s
    _, ss = ignore_space(ss)
    neg = False
    while True:
        #print("not iter", ss[:20])
        if ss[:1] == "!":
            neg = not neg
            ss = ss[1:]
        else:
            break
        _, ss = ignore_space(ss)
    #print(neg)
    if ss[:1] == "(":
        form, ss = read_formula(ss[1:])
        _, ss = ignore_space(ss)
        assert ss[0] == ")"
        ss = ss[1:]
    elif ss[:1] in "AEO":
        form, ss = read_formula(ss)
    else:
        form, ss = read_basic(ss)
    if neg:
        form = ("NOT", form)
    return form, ss

def read_infix_expr(s):
    #print("reading infix", repr(s))
    ss = s
    _, ss = ignore_space(ss)
    thing1, ss = read_dotted_token_list(ss)
    _, ss = ignore_space(ss)
    neg = False
    if ss[:2] == "~~":
        op = "~~"
        ss = ss[2:]
    elif ss[:1] == "~":
        op = "~"
        ss = ss[1:]
    elif ss[:1] == "=":
        op = "="
        ss = ss[1:]
    elif ss[:1] == "@":
        op = "@"
        ss = ss[1:]
    elif ss[:2] == "!=":
        op = "="
        neg = True
        ss = ss[2:]
    elif ss[:2] == "!@":
        op = "@"
        neg = True
        ss = ss[2:]
    elif ss[:3] == "!~~":
        op = "~~"
        neg = True
        ss = ss[3:]
    elif ss[:2] == "!~":
        op = "~"
        neg = True
        ss = ss[2:]
    else:
        return None, s
    _, ss = ignore_space(ss)
    thing2, ss = read_dotted_token_list(ss)
    _, ss = ignore_space(ss)

    if thing1 == None or thing2 == None:
        return None, s

    if op == "~":
        ret = ("ISNEIGHBOR", thing1, thing2), ss
    if op == "~~":
        ret = ("ISPROPERNEIGHBOR", thing1, thing2), ss
    if op == "@":
        ret = ("POSEQ", thing1, thing2), ss
    if op == "=":
        if thing1 in alphabet and thing2 in alphabet:
            if thing1 == thing2:
                ret = ("T",), ss
            else:
                ret = ("F",), ss
        elif thing1 in alphabet and thing2 not in alphabet:
            ret = ("HASVAL", thing2, thing1), ss
        elif thing2 in alphabet and thing1 not in alphabet:
            ret = ("HASVAL", thing1, thing2), ss
        else:
            ret = ("VALEQ", thing1, thing2), ss
    if neg:
        ret = ("NOT", ret[0]), ret[1]
    return ret
    

def read_call(s):
    #print("reading call", s)
    ss = s
    _, ss = ignore_space(ss)
    call = []
    while True:
        _, ss = ignore_space(ss)
        if ss[:1] == "(":
            #print ("subex")
            formu, ss = read_formula(ss[1:])
            #print(formu)
            assert ss[:1] == ")"
            ss = ss[1:]
            call.append(formu)
        else:
            name, ss = read_infix_expr(ss)
            if name != None:
                call.append(name)
            else:
                name, ss = read_dotted_token_list(ss) #read_name(ss)
                #print(name)
                if name != None:
                    call.append(name)
                else:
                    break
    _, ss = ignore_space(ss)
    if len(call) == 0:
        return None, s
    if len(call) == 1:
        return ("BOOL", call[0]), ss
    return ("CIRCUIT", tuple(call)), ss
    
def read_basic(s):
    ret, s = read_infix_expr(s)
    if ret:
        return ret, s
    ret, s = read_call(s)
    if ret:
        return ret, s
    raise Exception("Cannot read basic at " + s[:30])
    




#formula = """Ao let xor a b := (a & !b) | (!a & b) in
#formula = "xor (xor o o.up) o.dn"
#formula = "a.b"
#parsed = read_dotted_token_list(formula)
#parsed = read_call(formula) #
#parsed = parse(code)
#formula = """Ao let xor a b := (a & !b) | (!a & b) in
#xor (xor (o=1) (o.up=1)) (o.dn=1)"""
#parsed = read_formula(formula)

#a = bbb



#alphabet = [0, 1]

#print(read_basic_expression("p = o & (p = o | p = p)"))
#a = bbb


#print(read_basic_expression("!1 = u & u = 1 <-> u @ v & 1 = 0 | u = v"))
#print(read_bound("[u1]"))


#f = read_formula("""Ao let c u v := v = 1 & u ~ v in 
#       (Ed[o1] c o d) & (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q))""")

#print(read_simplex("dn (x,y,1) (x,y-1,0)"))

#print(ignore_space("""    -- moi

#--- Hello
#moi moi"""))


#a = bbb
#-- defines the SFT of identifying codes


#a = bbb
s = """
%nodes 0
%dim 2
%topology grid
%alphabet 0 1
%SFT fullshift              Ao 0 = 0
%SFT ver_golden_mean_shift  Ao o = 1 -> o.dn = 0
%SFT ver_golden_mean_shift2 Ao o = 1 -> o.dn = 0
%SFT hor_golden_mean_shift  Ao o = 1 -> o.rt = 1
%SFT golden_mean_shift      Ao o = 1 -> o.up = 1 & o.rt = 1
%equal ver_golden_mean_shift ver_golden_mean_shift2
"""

#print(parse(s))




"""
%SFT id_code
(x,y,0)=0 (x+1,y,0)=1
(x,y,0)=0 (x+1,y,0)=0
"""

"""
%set idcode Oo let c u v := v = 1 & u ~ v in   -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
"""




s = """
%nodes 0
%dim 2
%topology grid
%alphabet 0 1
%set idcode Oo let c u v := v = 1 & u ~ v in   -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
%density idcode
"""



"""
%set idcode Ao let c u v := v = 1 & u ~ v in -- v is code word neighbor of u
       (Ed[o1] c o d) &              -- o must have some code word neighbor, and
       (Ap[o2] p !@ o -> Eq[o1p1] (c o q & ! c p q) | (c p q & !c o q)) -- any pair is separated
"""

"""

"""

#parsed = parse(s)
#print(parsed)






