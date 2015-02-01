import copy
import operator

from collections import defaultdict, OrderedDict
from itertools import product as iter_product
from functools import reduce
from tabulate import tabulate
from random import random

##########################
# Introspected Functions #
##########################

class Ring(object):
    "A commutative semiring, called ring for brevity. \
    Inverse multiplication can be set to None if not available. \
    Then, variable elimination (adding evidence) will be unnormalized."
    def __init__(self, add, zero, mul, invmul, one):
        self.add = add
        self.zero = zero
        self.mul = mul
        self.invmul = invmul
        self.one = one

def unity(ring, domain=OrderedDict()):
    "Create a function that returns the ring's neutral element for any argument"
    def u(*args):
        return ring.one
    u.domain = domain
    return u

def arguments(f):
    "Return the ordered names of the arguments according to the domain information"
    return [var for var in f.domain.keys()]

def marginalize(f, ring, var):
    "Marginalize out the given variable according to the addition operator of the \
    ring and the domain of the variable"
    new_domain = f.domain.copy()
    del new_domain[var]
    eliminated_pos = arguments(f).index(var)
    results = {} # build a table with all assignment combinations
    for args in iter_product(*[new_domain[v] for v in new_domain.keys()]):
        expanded_args = list(args)
        expanded_args.insert(eliminated_pos, 'replace me')
        total = ring.zero
        for val in f.domain[var]:
            expanded_args[eliminated_pos] = val
            total = ring.add(total, f(*expanded_args))
        results[args] = total
    def marginalized(*args):
        return results[args]
    marginalized.domain = new_domain
    return marginalized

def marginalize_others(f, ring, keep_var):
    "Marginalize out all variables that are not (in) keep_var"
    if not type(keep_var) == list:
        keep_var = [keep_var]
    new_func = f
    for arg in arguments(f):
        if not arg in keep_var:
            new_func = marginalize(new_func, ring, arg)
    return new_func

def merge(f1, f2, ring):
    "The functions are merged using the ring's multiplication operator. \
    The new domain is made up of the union of the original domain's variables. \
    It is assumed that the domain per-variable does not change between the functions."
    new_domain = f1.domain.copy()
    new_domain.update(f2.domain.items()) # merge lines todo
    results = {}
    arg_list1 = arguments(f1)
    arg_list2 = arguments(f2)
    arg_list_total = list(new_domain.keys())
    for args in iter_product(*[dom for dom in new_domain.values()]):
        args1 = args[:len(arg_list1)]
        args2 = arg_list2[:]
        for i in range(len(args2)):
            pos = arg_list_total.index(arg_list2[i])
            args2[i] = args[pos]
        results[args] = ring.mul(f1(*args1), f2(*args2))
    def merged(*args):
        return results[args]
    merged.domain = new_domain
    return merged 

def eliminate(f, ring, var, value, normalize=False):
    "Set a variable to a fixed value (add evidence). The resuling function \
    can be normalized if an inverse multiplication operator is available."
    if not var in f.domain:
        return f
    varindex = arguments(f).index(var) # at which position is var?
    if normalize:
        var_only = marginalize_others(f, ring, var)
        normalization_constant = var_only(value)
    def eliminated(*args):
        args = args[:varindex] + (value,) + args[varindex:]
        result = f(*args)
        if normalize:
            return ring.invmul(result, normalization_constant)
        else:
            return result
    eliminated.domain = f.domain.copy() # todo [:]
    del eliminated.domain[var]
    return eliminated

def print_func_table(f):
    table = [( ("(" + ", ".join(arguments(f)) + ")", "value") )]
    for x in iter_product(*[f.domain[x] for x in arguments(f)]):
        table.append( (str(x), str(f(*x))) )
    print(tabulate(table, headers="firstrow"))

################
# Factor Graph #
################

class Message(object):
    def __init__(self, source, destination, func, variableinfos = {}):
        self.source = source
        self.destination = destination
        self.func = func
        self.variableinfos = variableinfos # used only for the split-factor extension

    def __repr__(self):
        return "<Message: %s -> %s,\tDomain: [%s], VariableInfos: [%s]>" % \
            (self.source.name, self.destination.name, ",".join(self.func.domain.keys()), \
             ",".join(self.variableinfos.keys()))

class Node(object):
    def send(self, message):
        recipient = message.destination
        recipient.received_messages[self.name] = message

    def reset(self):
        self.received_messages = {}

    def is_leaf(self):
        if len(self.neighbours) == 1:
            return True
        return False

    def get_target(self):
        "A node can only send to a neighbour if it has not already sent to that \
        neighbour and it has received messages from all other neighbours."
        needed_to_send = defaultdict(int)
        for target in self.neighbours:
            needed_to_send[target] = len(self.neighbours) - 1
        for _, message in self.received_messages.items():
            for target in self.neighbours:
                if message.source != target:
                    needed_to_send[target] -= 1
        for k, v in needed_to_send.items():
            if v == 0 and not self.name in k.received_messages:
                return k
        return None

class VariableNode(Node):
    def __init__(self, name, domain, ring, neighbours=[], remote_neighbours=[]):
        self.name = name
        self.domain = domain
        self.ring = ring
        self.neighbours = neighbours[:]
        self.remote_neighbours = remote_neighbours[:] # only needed for the split factor extension
        self.received_messages = {}

    def __repr__(self):
        return "<VariableNode: %s>" % self.name

    def marginal(self):
        f = unity(self.ring)
        for m in self.received_messages.values():
            f = merge(f, m.func, self.ring)
        f = marginalize_others(f, self.ring, self.name)
        return f

class FactorNode(Node):
    def __init__(self, name, func, ring, neighbours=[], remote_neighbours=[]):
        self.name = name
        self.func = func
        self.ring = ring
        self.neighbours = neighbours[:]
        self.remote_neighbours = remote_neighbours[:] # only used by the split factor extension
        self.received_messages = {}

    def __repr__(self):
        return "<VariableNode: %s>" % self.name

    def marginal(self):
        "The marginal over the domain of the function"
        f = self.func
        for m in self.received_messages.values():
            f = merge(f, m.func, self.ring)
        f = marginalize_others(f, self.ring, self.func.domain.keys())
        return f

class FactorGraph(object):
    def __init__(self, ring, variables = {}, factors = {}):
        self.ring = ring
        self.variables = variables
        self.factors = factors

    def addVariableNode(self, name, domain, neighbours=[], remote_neighbours=[]):
        v = VariableNode(name, domain, self.ring)
        self.variables[name] = v
        self.connect(v, neighbours)
        self.connect(v, remote_neighbours, True)
        return v

    def addFactorNode(self, name, func, neighbours=[], remote_neighbours=[]):
        v = FactorNode(name, func, self.ring)
        self.factors[name] = v
        self.connect(v, neighbours)
        self.connect(v, remote_neighbours, True)
        return v

    def connect(self, a, b, remote=False):
        "Make an edge between two nodes or between a source and several neighbours."
        if not isinstance(b, list):
            b = [b]
        for b_ in b:
            if remote:
                a.remote_neighbours.append(b_)
                b_.remote_neighbours.append(a)
            else:
                a.neighbours.append(b_)
                b_.neighbours.append(a)

    def message(self, source, target):
        "Construct a message between the source and the target node"
        if not target in source.neighbours:
            raise Exception("Cannot create a message to a non-neighbour")
        f = unity(self.ring, OrderedDict([(source.name, source.domain)])) if type(source) == VariableNode else source.func
        for neighbour, m in source.received_messages.items():
            if neighbour == target.name:
                continue
            f = merge(f, m.func, self.ring)
        f = marginalize_others(f, self.ring, target.name if source.name in self.factors else source.name)
        return Message(source, target, f)

    def merge_factors(self):
        return reduce(lambda f1, f2: merge(f1, f2, self.ring), [fn.func for fn in self.factors.values()])

##########################
# Split Factor Extension #
##########################

def find_max(f):
    "Find the argmax on the entire domain of the function by brute force"
    args = arguments(f)
    ma = None
    mav = float('-inf')
    for x in iter_product(*[f.domain[x] for x in args]):
        v = f(*x)
        if v > mav:
            ma, mav = x, v
    return {list(f.domain)[i]:ma[i] for i in range(len(args))}

class VariableInfo(object):
    def __init__(self, name, contained, neighbourcount, visitcount):
        self.name = name
        self.contained = contained # is the variable contained in the sending subgraph?
        self.neighbourcount = neighbourcount # neighbours + remote neighbours
        self.visitcount = visitcount # how many of the neighbours did the message visit?

def compute_variableinfos(source, target):
    "The variableinfos for the target node"
    variableinfos = {}
    if target.name in source.received_messages: # backwards pass
        return variableinfos
    # variableinfos the source received
    for sender, m in source.received_messages.items():
        for vi in m.variableinfos.values():
            if vi.name in variableinfos:
                variableinfos[vi.name].visitcount += vi.visitcount
                variableinfos[vi.name].contained |= vi.contained
            else:
                variableinfos[vi.name] = copy.deepcopy(vi)
    # update / add variableinfos for the source node
    if type(source) == VariableNode:
        if len(source.remote_neighbours) > 0:
            if not source.name in variableinfos:
                variableinfos[source.name] = VariableInfo(source.name, True, len(source.remote_neighbours) + len(source.neighbours), 0)
            else:
                variableinfos[source.name].contained = True
    else: # if type(source) == FactorNode:
        for n in source.remote_neighbours + source.neighbours:
            if len(n.remote_neighbours) > 0:
                if not n.name in variableinfos:
                    variableinfos[n.name] = VariableInfo(n.name, False, len(n.remote_neighbours) + len(n.neighbours), 1)
                else:
                    variableinfos[n.name].visitcount += 1
    return dict(filter(lambda x: x[1].neighbourcount > x[1].visitcount, variableinfos.items()))

def extended_message_domain(source, target, variableinfos):
    "The relevant domain of the receiving subgraph"
    if not target.name in source.received_messages: # forward pass
        domain = [source.name] if type(source) == VariableNode else [target.name] # standard message passing
        for var, vi in variableinfos.items():
            if var not in domain: # only uniques
                domain.append(var)
        return domain
    else: # backwards pass
        return list(source.received_messages[target.name].func.domain.keys())

def extended_message(source, target, ring):
    if not target in source.neighbours:
        raise Exception("Cannot create a message to a non-neighbour")
    f = unity(ring, OrderedDict([(source.name, source.domain)])) if type(source) == VariableNode else source.func
    for node, m in source.received_messages.items():
        if node == target.name:
            continue
        f = merge(f, m.func, ring)
    variableinfos = compute_variableinfos(source, target)
    message_domain = extended_message_domain(source, target, variableinfos)
    f = marginalize_others(f, ring, message_domain)
    return Message(source, target, f, variableinfos)

############
# Examples #
############

# Introspected Functions
########################

# ring = Ring(operator.add, 0, operator.mul, operator.truediv, 1) # plus-mul
ring = Ring(max, float('-inf'), operator.add, operator.sub, 0) # max-plus

def func1(x1, x2):
    return x1 * x2
func1.domain = OrderedDict([('x1',[1,2,3]), ('x2',[1,2,3])])

def func2(x2, x3):
    return x2 * x3
func2.domain = OrderedDict([('x2',[1,2,3]), ('x3',[1,2,3])])

c = merge(func1, func2, ring)
m = marginalize(c, ring, 'x2')
e = eliminate(c, ring, 'x3', 1)

print("## Examples for the introspected functions ##")
print(m(2,3))
print(arguments(m))
print(m.domain)
print_func_table(m)

# Factor Graph
##############

def variable_assignment(vn):
    "The assignment a variable shall take when message passing has finished"
    return find_max(vn.marginal())[vn.name]
        
def create_random_func(variables):
    results = {}
    for assignment in iter_product(*[var.domain for var in variables]):
        results[assignment] = random()
    def func(*a):
        return results[a]
    func.domain = OrderedDict([(var.name, var.domain) for var in variables])
    return func

G = FactorGraph(ring)
x1 = G.addVariableNode('x1', range(10))
x2 = G.addVariableNode('x2', range(10))
x3 = G.addVariableNode('x3', range(10))
x4 = G.addVariableNode('x4', range(10))
x5 = G.addVariableNode('x5', range(10))
x6 = G.addVariableNode('x6', range(10))
f12 = create_random_func([x1, x2])
a12 = G.addFactorNode('a12', f12, [x1, x2])
f23 = create_random_func([x2, x3])
a23 = G.addFactorNode('a23', f23, [x2, x3])
f34 = create_random_func([x3, x4])
a34 = G.addFactorNode('a34', f34, [x3, x4])
f45 = create_random_func([x4, x5])
a45 = G.addFactorNode('a45', f45, [x4, x5])
f56 = create_random_func([x5, x6])
a56 = G.addFactorNode('a56', f56, [x5, x6])

## Closing the loop
f161 = create_random_func([x1, x6])
a161 = G.addFactorNode('a16^1', f161, x1, x6)
f166 = create_random_func([x1, x6])
a166 = G.addFactorNode('a16^6', f166, x6, x1)

print("\n## Example for inference on a factor graph ##")
running = True
while(running):
    running = False
    for n in list(G.variables.values()) + list(G.factors.values()):
        t = n.get_target()
        if t:
            # m = G.message(n, t) # vanilla GDL messages for the non-loopy case
            m = extended_message(n, t, G.ring) # extended messages for loopy graphs with split factors
            print(m)
            n.send(m)
            running = True

print("Max assignment found with message passing:")
assignment = {}
for vn in G.variables.values():
    assignment[vn.name] = variable_assignment(vn)
print(assignment)

print("Max assignment found by brute force")
print("...computing...")
single_factor = G.merge_factors()
print(find_max(single_factor))
