"""
parse takes a string which represents a full program
in our language, and parses the entire program

token means string or integers or whatever
name is a string
"""

from fractions import Fraction
import parsy as p
from general import *
from enum import Enum, Flag, auto
from functools import reduce, wraps

### Top-level parsing functions

def parse_diddy(code):
    "Parse a Diddy file. Return a list of commands or raise a ParseError."
    return (whitespace >> diddy_file).parse(code)
    
def parse_formula(code):
    "Parse a FO formula."
    return (quantified | formula).parse(code)

### Common utilities

def many_strict(parser):
    """Parse zero or more times, return results in a list.
       Fail if the parser fails and consumes input.
       The purpose is to give better error messages than parser.many()."""

    @p.Parser
    def many_strict_parser(stream, index):
        values = []
        result = None
        while True:
            result = parser(stream, index).aggregate(result)
            if result.status:
                values.append(result.value)
                index = result.index
            elif result.furthest > index:
                return result
            else:
                return p.Result.success(index, values).aggregate(result)

    return many_strict_parser

# Whitespace and comments
whitespace = p.regex(r'(\s|--.*(\r|\n)+)*')

def lexeme(p):
    "p followed by whitespace."
    return p << whitespace

# Parentheses    
lparen = lexeme(p.string('('))
rparen = lexeme(p.string(')'))
lbracket = lexeme(p.string('['))
rbracket = lexeme(p.string(']'))
lbrace = lexeme(p.string('{'))
rbrace = lexeme(p.string('}'))
# Separators
period = lexeme(p.string('.'))
comma = lexeme(p.string(','))
colon = lexeme(p.string(':'))
semicolon = lexeme(p.string(';'))

# Protected keywords
keyword = p.regex(r'(let|in)(\W|$)')

# Range of nonnegative integers; "inf" means no upper bound
@p.generate
def natural_range():
    start = yield natural
    end = yield (lexeme(p.string('-')) >> natural.optional(default="inf")).optional(start)
    return (start, end)

# Set of nonnegative integers (union of ranges)
natural_set = natural_range.sep_by(comma, min=1)

### Command parser

class ArgType(Flag):
    LABEL = auto()
    NUMBER = auto()
    SIMPLE_LIST = auto()
    PATTERN_LIST = auto()
    NESTED_LIST = auto()
    PATTERN = auto()
    MAPPING = auto() # mainly for weights
    FORMULA = auto()
    TOPOLOGY_KEYWORD = auto()
                  
class Command:
    "A container for a Diddy command definition."
    
    def __init__(self, name, pos_args, opts=None, flags=None, aliases=None):
        self.name = name
        self.pos_args = pos_args
        if opts is None:
            opts = []
        self.opts = opts
        if flags is None:
            flags = []
        self.flags = flags
        if aliases is None:
            aliases = []
        self.aliases = aliases

# List of commands
# Each entry has command names, positional arguments and types, optional arguments (whose values are flat), and flags
commands = [
    # Setting up the environment
    Command("alphabet",
            [ArgType.SIMPLE_LIST | ArgType.MAPPING],
            opts = ["default"],
            aliases = ["alph"]),
    Command("topology",
            [ArgType.TOPOLOGY_KEYWORD | ArgType.NESTED_LIST]),
    Command("dim",
            [ArgType.NUMBER],
            opts = ["onesided"],
            aliases = ["dimension"]),
    Command("nodes",
            [ArgType.SIMPLE_LIST | ArgType.MAPPING],
            aliases = ["vertices"]),
    Command("set_weights",
            [ArgType.MAPPING]),

    # Defining objects
    Command("sft",
            [ArgType.LABEL, ArgType.FORMULA | ArgType.PATTERN_LIST],
            aliases = ["SFT"]),
    Command("compute_forbidden_patterns",
            [ArgType.LABEL],
            opts = ["radius"],
            aliases = ["calculate_forbidden_patterns"]),
    Command("wang",
            [ArgType.LABEL, "tiles", ArgType.NESTED_LIST],
            opts = ["inverses"],
            flags = ["topology", "use_topology", "custom_topology"],
            aliases = ["Wang"]),
    Command("CA",
            [ArgType.LABEL, ArgType.NESTED_LIST],
            aliases = ["cellular_automaton"]), 
    Command("compose_CA",
            [ArgType.LABEL, ArgType.SIMPLE_LIST]),
    Command("spacetime_diagram",
            [ArgType.LABEL, ArgType.LABEL],
            opts = ["time_axis"],
            flags = ["twosided"]),
    Command("TFG",
            [ArgType.LABEL, ArgType.NESTED_LIST],
            aliases = ["topological_full_group_element"]),

    # Printing objects' basic properties
    Command("show_formula",
            [ArgType.LABEL],
            aliases = ["print_formula"]),
    Command("show_parsed",
            [ArgType.LABEL],
            aliases = ["print_parsed"]),
    Command("show_forbidden_patterns",
            [ArgType.LABEL],
            aliases = ["print_forbidden_patterns"]),

    # Comparing objects
    Command("equal",
            [ArgType.LABEL, ArgType.LABEL],
            opts = ["method", "expect"]),
    Command("contains",
            [ArgType.LABEL, ArgType.LABEL],
            opts = ["method", "expect"]),
    Command("compare_sft_pairs", [],
            opts = ["method"],
            aliases = ["compare_SFT_pairs"]),
    Command("compare_sft_pairs_equality", [],
            opts = ["method"],
            aliases = ["compare_SFT_pairs_equality"]),
    Command("compute_CA_ball",
            [ArgType.NUMBER, ArgType.SIMPLE_LIST],
            opts = ["filename"],
            aliases = ["calculate_CA_ball"]),

    # Analyzing dynamical properties
    Command("minimum_density",
            [ArgType.LABEL, ArgType.SIMPLE_LIST],
            opts = ["threads", "mode", "chunk_size", "symmetry", "print_freq_pop", "print_freq_cyc", "expect"],
            flags = ["verbose", "rotate"]),
    Command("density_lower_bound",
            [ArgType.LABEL, ArgType.SIMPLE_LIST, ArgType.SIMPLE_LIST],
            opts = ["radius", "print_freq", "expect"],
            flags = ["verbose", "show_rules"]),
    Command("entropy_upper_bound",
            [ArgType.LABEL, ArgType.SIMPLE_LIST],
            opts = ["radius"]),
    Command("entropy_lower_bound",
            [ArgType.LABEL, ArgType.SIMPLE_LIST, ArgType.SIMPLE_LIST]),
    Command("TFG_loops",
            [ArgType.LABEL, ArgType.LABEL],
            aliases = ["topological_full_group_element_loops"]),

    # Visualization
    Command("tiler",
            [ArgType.LABEL]),
    Command("tile_box",
            [ArgType.LABEL, ArgType.NUMBER]),
    Command("keep_tiling",
            [ArgType.LABEL],
            opts = ["min", "max"]),

    # Technical commands
    Command("start_cache",
            [ArgType.NUMBER, ArgType.NUMBER]),
    Command("end_cache", [])
]

command_dict = {alias : cmd for cmd in commands for alias in [cmd.name] + cmd.aliases}

# Unsigned integer (can be used as label)
natural = lexeme(p.regex(r'0|[1-9]\d*').map(int))
# Negative integer
neg_nat = (p.string('-') >> natural).map(lambda n: -n)
# Signed integer
integer = natural | neg_nat
# Fraction
@p.generate("fraction")
def fraction():
    numerator = yield integer
    maybe_denominator = yield (lexeme(p.string('/')) >> natural).optional()
    if maybe_denominator is None:
        return numerator
    else:
        return Fraction(numerator, maybe_denominator)

# Labels (of commands, alphabets, nodes etc.)
label = lexeme(keyword.should_fail("keyword") >> p.regex(r'[a-zA-Z]\w*')).desc("label")
topology_keyword = lexeme(p.regex(r'line|grid|square|squaregrid|king|kinggrid|triangle|trianglegrid|hex|hexgrid')).desc("topology name")

# Optional argument / setter; value is a signed number or label
# Type checking is not done at parse time
@p.generate("optional argument / setter")
def set_arg_value():
    arg_name = yield label
    yield p.string('=')
    arg_value = yield fraction | label | nested_list
    return (arg_name, arg_value)
    
# Node name: period-separated sequence of labels
node_name = (label | natural).sep_by(period, min=1).map(lambda items: items[0] if len(items) == 1  else tuple(items))

# Vector or node vector
@p.generate("vector")
def vector():
    yield lparen
    nums = yield integer.sep_by(comma << p.peek(integer))
    maybe_node = yield (comma >> node_name).optional()
    yield rparen
    if maybe_node is None:
        return tuple(nums)
    else:
        return tuple(nums + [maybe_node])
    
# Pattern/mapping pair
def mapping_pair(key, value):
    @p.generate("mapping pair")
    def part():
        the_key = yield key
        yield colon
        val = yield value
        return (the_key, val)
    return part

# Mapping: list of key:value pairs, parsed into a dict
def mapping(key, value):
    return (lbrace >> mapping_pair(key, value).many().map(dict) << rbrace).desc("mapping")
def nested_mapping(key, value):
    @p.generate
    def nested_map():
        the_map = yield mapping(key, value | nested_mapping(key, value))
        return the_map
    return nested_map
# Mapping without braces
def open_mapping(key, value):
    return mapping_pair(key, value).many().map(dict).desc("mapping")

# Pattern: vector:label/number mapping
pattern = mapping(vector, label|fraction)
open_pattern = open_mapping(vector, label|fraction)

# Flat value
flat_value = vector | set_arg_value.desc("setter") | node_name | fraction | pattern

# List (possibly nested) of numbers, vectors, labels, setters and patterns
@p.generate("list")
def nested_list():
    yield lbracket
    vals = yield (quantified | flat_value | nested_list).many()
    yield rbracket
    return vals
    
# List without braces
open_nested_list = nested_list.many().desc("list")

# Parse a specific command based on its definition (do not parse the label)
# TODO: finish
# Once there are only list arguments left, it's possible to switch into "list mode" and read semicolon-separated open lists
# If there is only one list argument left, it's possible to switch into "nested list mode" or "pattern mode" and read semicolon-separated open lists or open patterns, and pack them into a single list argument
def command_args(cmd, index, args=None, opts=None, flags=None, mode="normal"):
    if args is None:
        args = []
        opts = dict()
        flags = set()
    #print("command", cmd.name, "index", index, "mode", mode, "prev", args)
    
    @p.generate
    def parse_args():
        nonlocal index
        if mode == "normal":
            # We are actually reading arguments
            if index >= 0:
                # Normal mode: parse options and keywords until a positional argument appears
                while True:
                    maybe_flag = yield (p.string('@') >> label).desc("flag").optional()
                    if maybe_flag is not None:
                        flags.append(maybe_flag)
                        continue
                    maybe_opt = yield set_arg_value.optional()
                    if maybe_opt is not None:
                        name, value = maybe_opt
                        opts[name] = value
                        continue
                    break
                # No more optional, keyword or positional arguments: return all data
                if index == len(cmd.pos_args):
                    return (cmd.name, args, opts, flags)
                # Choose the argument parser(s) based on its expected type and try to apply each
                # Accept the first one that succeeds
                arg_type = cmd.pos_args[index]
                arg_parsers = []
                if ArgType.TOPOLOGY_KEYWORD in arg_type:
                    arg_parsers.append(topology_keyword)
                if ArgType.LABEL in arg_type:
                    arg_parsers.append(label)
                if ArgType.NUMBER in arg_type:
                    arg_parsers.append(fraction)
                if ArgType.SIMPLE_LIST in arg_type or ArgType.NESTED_LIST in arg_type or ArgType.PATTERN_LIST in arg_type:
                    arg_parsers.append(nested_list)
                if ArgType.PATTERN in arg_type:
                    arg_parsers.append(pattern)
                if ArgType.MAPPING in arg_type:
                    arg_parsers.append(nested_mapping(flat_value, flat_value | nested_list))
                if ArgType.FORMULA in arg_type:
                    arg_parsers.append(quantified)
                arg = yield p.alt(*arg_parsers)
                args.append(arg)
            # Choose the mode for the remaining arguments
            # Normal mode is the default
            next_modes = [command_args(cmd, index+1, args, opts, flags, "normal")]
            # Non-normal modes can be forced with a semicolon, if applicable
            # If we only have simple list arguments left, try list mode
            if index < len(cmd.pos_args)-1 and all(ArgType.SIMPLE_LIST in typ or ArgType.MAPPING in typ for typ in cmd.pos_args[index+1:]):
                next_modes.append(semicolon.optional() >> command_args(cmd, index+1, args.copy(), opts.copy(), flags.copy(), "list"))
            # If we have only one list argument left, try nested list or pattern modes
            if index == len(cmd.pos_args)-2 and ArgType.NESTED_LIST in cmd.pos_args[index+1]:
                next_modes.append(semicolon.optional() >> command_args(cmd, index+1, args.copy(), opts.copy(), flags.copy(), "nested_list"))
            if index == len(cmd.pos_args)-2 and ArgType.PATTERN_LIST in cmd.pos_args[index+1]:
                next_modes.append(semicolon.optional() >> command_args(cmd, index+1, args.copy(), opts.copy(), flags.copy(), "pattern_list"))
            ret = yield p.alt(*next_modes)
            return ret
        elif mode == "list":
            # List mode: read remaining arguments as semicolon-separated open lists
            # Flags can be read, but optional arguments cannot, as they're interpreted as assignments
            # May also read a mapping
            while index <= len(cmd.pos_args):
                curr_collection = None
                while True:
                    # Optional argument
                    maybe_flag = yield (p.string('@') >> label).desc("flag").optional()
                    if maybe_flag is not None:
                        flags.append(maybe_flag)
                        continue
                    # Semicolon: finish current list and begin the next one
                    # Also finish if we ran out of arguments
                    maybe_sep = yield semicolon.optional()
                    if maybe_sep:
                        break
                    # Otherwise, read an item and store it to the list
                    maybe_pair = yield mapping_pair(flat_value, flat_value | nested_list).optional()
                    if maybe_pair is not None:
                        if curr_collection is None:
                            curr_collection = dict()
                        if type(curr_collection) == dict:
                            curr_collection[maybe_pair[0]] = maybe_pair[1]
                        else:
                            yield p.fail("list item")
                    else:
                        maybe_item = yield flat_value.optional()
                        if maybe_item is not None:
                            if curr_collection is None:
                                curr_collection = []
                            if type(curr_collection) == list:
                                curr_collection.append(maybe_item)
                            else:
                                yield p.fail("mapping item")
                        else:
                            break
                # Store current list and increment index
                args.append(curr_collection)
                index += 1
            return (cmd.name, args, opts, flags)
        elif mode == "nested_list":
            # Nested list mode: read the one remaining argument as a semicolon-separated list of open lists
            # Flags can be read, but not options
            lists = []
            finding = True
            while finding:
                curr_list = []
                while True:
                    # Optional argument
                    maybe_flag = yield (p.string('@') >> label).desc("flag").optional()
                    if maybe_flag is not None:
                        flags.append(maybe_flag)
                        continue
                    # Semicolon: finish current list and begin the next one
                    # Also finish if we ran out of arguments
                    maybe_sep = yield semicolon.optional()
                    if maybe_sep:
                        break
                    # Otherwise, read an item and store it to the list
                    item = yield (quantified | flat_value | nested_list).optional()
                    if item is None:
                        finding = False
                        break
                    else:
                        curr_list.append(item)
                lists.append(curr_list)
            return (cmd.name, args+[lists], opts, flags)
        elif mode == "pattern_list":
            # As above, but with semicolon-separated open patterns
            patterns = []
            finding = True
            while finding:
                curr_pat = dict()
                while True:
                    # Optional argument
                    maybe_flag = yield (p.string('@') >> label).desc("flag").optional()
                    if maybe_flag is not None:
                        flags.append(maybe_flag)
                        continue
                    # Semicolon: finish current list and begin the next one
                    # Also finish if we ran out of arguments
                    maybe_sep = yield semicolon.optional()
                    if maybe_sep:
                        break
                    # Otherwise, read an item and store it to the list
                    pair = yield mapping_pair(flat_value, flat_value | nested_list).optional()
                    #print("pair", pair)
                    if pair is None:
                        finding = False
                        break
                    else:
                        curr_pat[pair[0]] = pair[1]
                patterns.append(curr_pat)
            return (cmd.name, args+[patterns], opts, flags)
        else:
            raise Exception("Unknown parse mode: " + mode)
        
    return parse_args

# Parse any command
@p.generate
def command():
    yield p.string('%')
    alias = yield label
    try:
        com = yield command_args(command_dict[alias], -1)
        return com
    except KeyError:
        yield p.fail("valid command name")

# Parse a full Diddy file
diddy_file = many_strict(command)


### Formula parser

# Operator associativity
# Prefix, left and right are self-explanatory
# Flatten collects all arguments into a single list (the operator is associative)
# Chain joins the propositions with ANDs
class Assoc(Flag):
    PREFIX = auto()
    LEFT = auto() # unused for now
    RIGHT = auto()
    FLATTEN = auto()
    CHAIN = auto()
    STRICT_CHAIN = auto()
    
# Create a parser out of a precedence table
def expr_with_ops(prec_table, atomic, prec_index=0):

    if prec_index == len(prec_table):
        return atomic
        
    else:
        @p.generate(prec_table[prec_index][0] + " expression")
        def parse_the_expr():
            name, assoc, operators = prec_table[prec_index]
            #print("parsing", name, "expression, precedence", prec_index)
            parse_next = expr_with_ops(prec_table, atomic, prec_index=prec_index+1)
            if assoc == Assoc.PREFIX:
                # Parse a chain of prefix operators
                prefixes = yield p.alt(*operators).many()
                value = yield parse_next
                ret = reduce(lambda val, op: op(val), reversed(prefixes), value)
            elif assoc == Assoc.LEFT:
                # Parse tokens separated by a left associative operator
                raise NotImplementedError
            elif assoc == Assoc.RIGHT:
                # Parse tokens separated by a right associative operator
                first = yield parse_next
                maybe_others = yield p.alt(*operators).bind(lambda op: parse_the_expr.map(lambda second: op(first, second))).optional()
                if maybe_others is not None:
                    #print("Parsed many", maybe_others, "at level", table_ix, assoc_name[table_ix])
                    ret = maybe_others
                else:
                    #print("Parsed one", first, "at level", table_ix, assoc_name[table_ix])
                    ret = first
            elif assoc == Assoc.FLATTEN:
                # Parse tokens separated by a flattening operator
                op_parser, op_func = operators
                values = yield parse_next.sep_by(op_parser, min=1)
                if len(values) > 1:
                    #print("Parsed many", values, "at level", table_ix, assoc_name[table_ix])
                    ret = op_func(values)
                else:
                    #print("Parsed one", values, "at level", table_ix, assoc_name[table_ix])
                    ret = values[0]
            elif assoc in Assoc.CHAIN | Assoc.STRICT_CHAIN:
                # Parse tokens separated by a chained operator
                first = yield parse_next
                maybe_others = yield p.alt(*operators).bind(lambda op: parse_next.map(lambda val: (op, val))).at_least(1 if assoc == Assoc.STRICT_CHAIN else 0)
                if len(maybe_others) == 1:
                    op, val = maybe_others[0]
                    #print("Parsed two", op(first, val), "at level", table_ix, assoc_name[table_ix])
                    ret = op(first, val)
                elif maybe_others:
                    propositions = ["AND"]
                    for (op, val) in maybe_others:
                        propositions.append(op(first, val))
                        first = val
                    #print("Parsed many", propositions, "at level", table_ix, assoc_name[table_ix])
                    ret = tuple(propositions)
                else:
                    #print("Parsed one", first, "at level", table_ix, assoc_name[table_ix])
                    ret = first
            #print("parsed", ret)
            return ret
        return parse_the_expr

# Alphabetic label
strict_label = lexeme((keyword | p.regex(r'[AEO].*')).should_fail("keyword") >> p.regex(r'[a-zA-Z_]+')).desc("formula variable")

# Positional expression
pos_expr = p.seq(strict_label | integer.desc("integer"),
                 (lexeme(p.string('.')) >> (label | integer | vector | p.string('')).desc("address")).many()).combine(lambda var, addrs: ("ADDR", var, *addrs) if addrs else var)

# Distance operator: specify allowed distances between two nodes
@p.generate
def dist_operation():
    neg = yield p.string('!').optional()
    yield lexeme(p.string('~^'))
    dist_ranges = yield natural_set
    if neg:
        return lambda x, y: ("NOT", ("HASDIST", dist_ranges, x, y))
    else:
        return lambda x, y: ("HASDIST", dist_ranges, x, y)

# Chainable comparison operators
comp_table = [("node comparison", Assoc.STRICT_CHAIN,
               [lexeme(p.string('~~')) >> p.success(lambda x, y: ("ISPROPERNEIGHBOR", x, y)),
                dist_operation,
                lexeme(p.string('~')) >> p.success(lambda x, y: ("ISNEIGHBOR", x, y)),
                lexeme(p.string('=')) >> p.success(lambda x, y: ("VALEQ", x, y)),
                lexeme(p.string('@')) >> p.success(lambda x, y: ("POSEQ", x, y)),
                lexeme(p.string('!~~')) >> p.success(lambda x, y: ("NOT", ("ISPROPERNEIGHBOR", x, y))),
                lexeme(p.string('!~')) >> p.success(lambda x, y: ("NOT", ("ISNEIGHBOR", x, y))),
                lexeme(p.string('!=')) >> p.success(lambda x, y: ("NOT", ("VALEQ", x, y))),
                lexeme(p.string('!@')) >> p.success(lambda x, y: ("NOT", ("POSEQ", x, y)))])]

# Atomic proposition that compares nodes
node_expr = expr_with_ops(comp_table, pos_expr)

# Function call
@p.generate("boolean variable or function call")
def bool_or_call():
    #print("parsing call")
    name = yield strict_label
    args = yield (pos_expr | lparen >> formula << rparen).many()
    #print("parsed call", name, args)
    if args:
        return ("CALL", name, *args)
    else:
        return ("BOOL", name)

# Restrictions in quantifiers
@p.generate("restriction part")
def restriction():
    name = yield strict_label
    num = yield natural
    return (name, num)

restrictions = lexeme(p.string('[')) >> restriction.many() << lexeme(p.string(']')).desc("variable restriction")

# Logical quantifier, potentially restricted
@p.generate("quantified formula")
def quantified():
    #print("parsing quantified")
    the_quantifier = yield p.alt(p.string("AC") >> p.success("CELLFORALL"),
                                 p.string("EC") >> p.success("CELLEXISTS"),
                                 p.string("OC") >> p.success("CELLORIGIN"),
                                 p.string("A") >> p.success("NODEFORALL"),
                                 p.string("E") >> p.success("NODEEXISTS"),
                                 p.string("O") >> p.success("NODEORIGIN"))
    var = yield strict_label
    restr = yield restrictions.map(dict).optional()
    #print("parsed quantifier part", the_quantifier, var)
    the_formula = yield formula
    return (the_quantifier, var, restr or dict(), the_formula)

# Table of operators and their associativities
# The first operator binds the loosest, the last one the tightest
# Prefix expects a list of parsers that return a unary function
# Left, right and chain expect a list of parsers that return binary functions (TODO: maybe they should be pairs instead)
# Flatten expects a pair (parser, variable-arity function)
boolean_ops = [
    # Logical connectives
    ("implication", Assoc.RIGHT, [lexeme(p.string('->')) >> p.success(lambda x, y: ("IMP", x, y))]),
    ("equivalence", Assoc.CHAIN, [lexeme(p.string('<->')) >> p.success(lambda x, y: ("IFF", x, y))]),
    ("disjunction", Assoc.FLATTEN, (lexeme(p.string('|')), lambda xs: ("OR",) + tuple(xs))),
    ("conjunction", Assoc.FLATTEN, (lexeme(p.string('&')), lambda xs: ("AND",) + tuple(xs))),
    # Negation
    ("negation", Assoc.PREFIX, [lexeme(p.string('!')) >> p.success(lambda x: ("NOT", x))])
    ]

# A let-in definition
@p.generate("let expression")
def let_expr():
    yield lexeme(p.string('let'))
    call = yield strict_label.at_least(1)
    yield lexeme(p.string(':='))
    result = yield formula
    yield lexeme(p.string('in'))
    rest = yield formula
    return ("LET", tuple(call), result, rest)

# A full formula
formula = p.forward_declaration()
formula.become(expr_with_ops(boolean_ops, quantified | let_expr | node_expr | bool_or_call | (lparen >> formula << rparen)))

### Testing



#print(read_formula("0"))


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






