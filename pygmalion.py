import copy
import inspect
import operator

from collections import defaultdict
from itertools import product as iter_product
from tabulate import tabulate

from random import random
from functools import reduce

##########################
# Introspected Functions #
##########################

# The function objects stored in the factors and passed with the messages need to have additional attributes:
# - domains: A dict that maps variable names to domains. A domain is a list of all possible values
# - (argspec: A list of the argument variable names. Is not needed if the function has "proper" named arguments)

# Examples
# ========
#
# ring = Ring(operator.add, 0, operator.mul, operator.truediv, 1)

# def func1(x1, x2):
#     return x1 * x2

# func1.domains = {'x1':[1,2,3], 'x2':[1,2,3]}

# def func2(x2, x3):
#     return x2 * x3

# func2.domains = {'x2':[1,2,3], 'x3':[1,2,3]}

# c = combine(func1, func2, ring)
# m = marginalize(c, ring, 'x2')
# e = eliminate(c, ring, 'x3', 1)
# print(m(2,3))
# print(get_args(m))
# print(m.domains)

class Ring(object):
    "A commutative semiring, called ring for brevity. \
    Inverse multiplication can be set to None if not available."
    def __init__(self, add, zero, mul, invmul, one):
        self.add = add
        self.zero = zero
        self.mul = mul
        self.invmul = invmul
        self.one = one

def get_args(f):
    "Return the names of the arguments of a function as a list of strings"
    if hasattr(f, 'argspec'):
        return f.argspec[:]
    return inspect.getargspec(f).args

def marginalize(f, ring, var):
    "Marginalize out the given variable according to the addition operator of the \
    ring and the domain of the variable"
    arg_spec = get_args(f)
    new_spec = arg_spec[:]
    new_spec.remove(var)
    eliminated_pos = arg_spec.index(var)

    results = {}
    for args in iter_product(*[f.domains[v] for v in new_spec]):
        expanded_args = list(args)
        expanded_args.insert(eliminated_pos, 'replace me')
        total = ring.zero
        for val in f.domains[var]:
            expanded_args[eliminated_pos] = val
            total = ring.add(total, f(*expanded_args))
        results[args] = total

    def marginalized(*args):
        return results[args]

    marginalized.argspec = new_spec
    marginalized.domains = f.domains.copy()
    del marginalized.domains[var]
    return marginalized

def marginalize_others(f, ring, keep_var):
    "Marginalize out all variables that are not (in) keep_var"
    if not type(keep_var) is list:
        keep_var = [keep_var]
    new_func = copy.deepcopy(f)
    for arg in get_args(f):
        if not arg in keep_var:
            new_func = marginalize(new_func, ring, arg)
    return new_func

def combine(f1, f2, ring):
    "The functions are merged using the ring's multiplication operator. \
    The new domain is made up of the union of the original domain's variables. \
    For example: combined(x1, x2, x3) = f1(x1, x2) * f2(x2, x3)"
    arg_spec1 = get_args(f1)
    arg_spec2 = get_args(f2)
    new_spec = arg_spec1[:]
    for arg in arg_spec2:
        if not arg in new_spec:
            new_spec.append(arg)
    new_domains = {}
    for arg in new_spec:
        if arg in arg_spec1:
            new_domains[arg] = f1.domains[arg]
        else:
            new_domains[arg] = f2.domains[arg]

    results = {}
    for args in iter_product(*[new_domains[var] for var in new_spec]):
        args1 = args[:len(arg_spec1)]
        args2 = arg_spec2[:]
        for i in range(len(args2)):
            pos = new_spec.index(arg_spec2[i])
            args2[i] = args[pos]
        results[args] = ring.mul(f1(*args1), f2(*args2))

    def combined(*args):
        return results[args]

    combined.argspec = new_spec
    combined.domains = new_domains
    return combined

def eliminate(f, ring, var, value, normalize=False):
    "Set a variable to a fixed value (e.g. add evidence). \
    The resuling function can be normalized if an inverse \
    multiplication operator is available"
    if not var in f.domains:
        return f
    new_domains = f.domains.copy()
    del new_domains[var]
    new_spec = get_args(f)
    varindex = new_spec.index(var) # at which position is var?
    new_spec.remove(var)

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

    eliminated.argspec = new_spec
    eliminated.domains = new_domains
    return eliminated

def print_func_table(f):
    table = [( ("(" + ", ".join(get_args(f)) + ")", "value") )]
    for x in iter_product(*[f.domains[x] for x in get_args(f)]):
        table.append( (str(x), str(f(*x))) )
    print(tabulate(table, headers="firstrow"))

def max_assignment(f):
    "Find the argmax on the entire domain of the function by brute force"
    arg_spec = get_args(f)
    ma = None
    mav = float('-inf')
    for x in iter_product(*[f.domains[x] for x in arg_spec]):
        v = f(*x)
        if v > mav:
            ma = x
            mav = v
    return {arg_spec[i]:ma[i] for i in range(len(arg_spec))}

########################
# Factor Graph Classes #
########################

class VariableInfo(object):
    def __init__(self, name, contained, neighbourcount, counter):
        self.name = name
        self.contained = contained
        self.neighbourcount = neighbourcount
        self.counter = counter

class Message(object):
    def __init__(self, source, destination, func, assignments = {}, variableinfos = {}):
        self.source = source
        self.destination = destination
        self.func = func
        self.variableinfos = variableinfos
        self.assignments = assignments

    def __repr__(self):
        return "<Message: %s -> %s,\tDomain: [%s], Assignments: [%s], VariableInfos: [%s]>" % \
            (self.source.name, self.destination.name, ",".join(self.func.domains.keys()), \
             ",".join(self.assignments.keys()), ",".join(self.variableinfos.keys()))

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

    def updated_variableinfos(self, target_node):
        "The variable infos for the target node"
        vis = {}
        for source, m in self.received_messages.items(): # include also the messages from the target node
            for vi in m.variableinfos.values():
                if vi.name in vis:
                    vis[vi.name].counter += vi.counter
                    vis[vi.name].contained |= vi.contained
                else:
                    vis[vi.name] = copy.deepcopy(vi)
        if type(self) == VariableNode:
            if len(self.remote_neighbours) > 0:
                if not self.name in vis:
                    vis[self.name] = VariableInfo(self.name, True, len(self.remote_neighbours) + len(self.neighbours), 0)
                else:
                    vis[self.name].contained = True
        else: # if type(self) == FactorNode:
            for n in self.remote_neighbours + self.neighbours:
                if len(n.remote_neighbours) == 0:
                    continue
                if not n.name in vis:
                    vis[n.name] = VariableInfo(n.name, False, len(n.remote_neighbours) + len(n.neighbours), 1)
                else:
                    vis[n.name].counter += 1
        return vis

    def reduced_domain(self, target_node, variableinfos):
        "The relevant domain of the receiving subgraph"
        rd = [self.name] if type(self) == VariableNode else [target_node.name] # the standard domain for message passing
        if not target_node.name in self.received_messages: # forward pass
            for var, vi in variableinfos.items():
                if vi.neighbourcount > vi.counter: # don't send variables to subgraphs that do not depend on it
                    rd.append(var)
        else: # backwards pass
            m = self.received_messages[target_node.name]
            for var in m.variableinfos.keys():
                if not var in rd:
                    rd.append(var)
        return list(set(rd)) # only uniques
            
class VariableNode(Node):
    def __init__(self, name, domain, ring, neighbours=[], remote_neighbours=[]):
        self.name = name
        self.domain = domain
        self.neighbours = neighbours[:]
        self.remote_neighbours = remote_neighbours[:]
        self.received_messages = {}
        self.ring = ring
        self.max_assignment = None
        self.assignments = {}

        def unity(x):
            return self.ring.one
        unity.domains = {name:domain}
        unity.argspec = [name]
        self.unity = unity

    def __repr__(self):
        return "<VariableNode: %s>" % self.name

    def message(self, target_node):
        f = self.unity
        for source, m in self.received_messages.items():
            if source == target_node:
                continue
            f = combine(f, m.func, ring)
        f = marginalize_others(f, self.ring, self.name)
        return Message(self, target_node, f)

    def extended_message(self, target_node):
        backwards = target_node.name in self.received_messages
        vis = self.updated_variableinfos(target_node)
        rd = self.reduced_domain(target_node, vis)
        f = self.unity
        for source, m in self.received_messages.items():
            if source == target_node:
                continue
            f = combine(f, m.func, ring)
        
        ass = self.assignments # assignments are only used for the backwards pass
        for m in self.received_messages.values():
            for var, val in m.assignments.items():
                ass[var] = val
                f = eliminate(f, self.ring, var, val)

        if backwards:
            f_total = combine(f, self.received_messages[target_node.name].func, self.ring)
            for var, val in ass.items():
                f_total = eliminate(f, self.ring, var, val)
            new_assignments = max_assignment(f_total)
            for var, val in new_assignments.items():
                if var in rd:
                    ass[var] = val
                    f = eliminate(f, self.ring, var, val)

        if self.name in ass:
            self.max_assignment = ass[self.name]
                    
        f = marginalize_others(f, self.ring, rd)
        return Message(self, target_node, f, ass, vis)

    def final_assignment(self):
        if self.max_assignment:
            return self.max_assignment
        
        for m in self.received_messages.values():
            if self.name in m.assignments:
                return m.assignments[self.name]

        f = self.unity
        for m in self.received_messages.values():
            f = combine(f, m.func, ring)

        for m in self.received_messages.values():
            for var, val in m.assignments.items():
                if var in f.domains:
                    f = eliminate(f, self.ring, var, val)
        f = marginalize_others(f, self.ring, self.name)
        ma = max_assignment(f)
        return ma[self.name]

class FactorNode(Node):
    def __init__(self, name, func, ring, neighbours=[], remote_neighbours=[]):
        self.name = name
        self.ring = ring
        self.func = func
        self.neighbours = neighbours[:]
        self.remote_neighbours = remote_neighbours[:]
        self.received_messages = {}
        self.assignments = {}

    def __repr__(self):
        return "<VariableNode: %s>" % self.name

    def message(self, target_node):
        f = self.func
        for neighbour in self.neighbours:
            if neighbour == target_node or not self.received_messages[neighbour.name]:
                continue
            f = combine(f, self.received_messages[neighbour.name].func, self.ring)
        f = marginalize_others(f, self.ring, target_node.name)
        return Message(self, target_node, f)

    def extended_message(self, target_node):
        backwards = target_node.name in self.received_messages
        vis = self.updated_variableinfos(target_node)
        rd = self.reduced_domain(target_node, vis)
        f = self.func
        for source, m in self.received_messages.items():
            if source == target_node:
                continue
            f = combine(f, m.func, self.ring)

        ass = self.assignments # eliminate the received assignments from f
        for m in self.received_messages.values():
            for var, val in m.assignments.items():
                ass[var] = val
                f = eliminate(f, self.ring, var, val)
        
        if backwards:
            f_total = combine(f, self.received_messages[target_node.name].func, self.ring)
            for var, val in ass.items():
                f_total = eliminate(f, self.ring, var, val)
            new_assignments = max_assignment(f_total)
            for var, val in new_assignments.items():
                if var in rd:
                    ass[var] = val
                    f = eliminate(f, self.ring, var, val)

        f = marginalize_others(f, self.ring, rd)
        return Message(self, target_node, f, ass, vis)

class FactorGraph(object):
    def __init__(self, ring, variables = {}, factors = {}):
        self.ring = ring
        self.variables = variables
        self.factors = factors

    def connect(self, a, b, remote=False):
        "Make an edge between two nodes or between a source and several neighbours."
        if not isinstance(b, list):
            b = [b]
        if a in self.variables:
            vn = self.variables[a]
            for b_ in b:
                fn = self.factors[b_]
                if not remote:
                    vn.neighbours.append(fn)
                    fn.neighbours.append(vn)
                else:
                    vn.remote_neighbours.append(fn)
                    fn.remote_neighbours.append(vn)
        else:
            fn = self.factors[a]
            for b_ in b:
                vn = self.variables[b_]
                if not remote:
                    vn.neighbours.append(fn)
                    fn.neighbours.append(vn)
                else:
                    vn.remote_neighbours.append(fn)
                    fn.remote_neighbours.append(vn)

    def factorize(self):
        return reduce(lambda f1, f2: combine(f1, f2, self.ring), [fn.func for fn in self.factors.values()])
            
############
# Examples #
############
        
def random_func(domains):
    spec = list(domains.keys())
    results = {}
    for args in iter_product(*[domains[v] for v in spec]):
        results[args] = random()
        
    def func(*args):
        return results[args]

    func.argspec = spec
    func.domains = domains
    return func

ring = Ring(max, float('-inf'), operator.add, operator.sub, 0)

def func1(x1, x2):
    return x1 * x2
func1.domains = {'x1':[1,2,3], 'x2':[1,2,3]}

def func2(x2, x3):
    return x2 * x3
func2.domains = {'x2':[1,2,3], 'x3':[1,2,3]}

c = combine(func1, func2, ring)
m = marginalize(c, ring, 'x2')
e = eliminate(c, ring, 'x3', 1)

G = FactorGraph(ring)
G.variables['x1'] = VariableNode('x1', range(10), ring)
G.variables['x2'] = VariableNode('x2', range(10), ring)
G.variables['x3'] = VariableNode('x3', range(10), ring)
G.variables['x4'] = VariableNode('x4', range(10), ring)
G.variables['x5'] = VariableNode('x5', range(10), ring)
G.variables['x6'] = VariableNode('x6', range(10), ring)

f12 = random_func({'x1':G.variables['x1'].domain, 'x2':G.variables['x2'].domain})
G.factors['a12'] = FactorNode('a12', f12, ring)
f23 = random_func({'x2':G.variables['x2'].domain, 'x3':G.variables['x3'].domain})
G.factors['a23'] = FactorNode('a23', f23, ring)
f34 = random_func({'x3':G.variables['x3'].domain, 'x4':G.variables['x4'].domain})
G.factors['a34'] = FactorNode('a34', f34, ring)
f45 = random_func({'x4':G.variables['x4'].domain, 'x5':G.variables['x5'].domain})
G.factors['a45'] = FactorNode('a45', f45, ring)
f56 = random_func({'x5':G.variables['x5'].domain, 'x6':G.variables['x6'].domain})
G.factors['a56'] = FactorNode('a56', f56, ring)
G.connect('a12', ['x1', 'x2'])
G.connect('a23', ['x2', 'x3'])
G.connect('a34', ['x3', 'x4'])
G.connect('a45', ['x4', 'x5'])
G.connect('a56', ['x5', 'x6'])

f161 = random_func({'x1':G.variables['x1'].domain, 'x6':G.variables['x6'].domain})
G.factors['a16^1'] = FactorNode('a16^1', f161, ring)
f166 = random_func({'x1':G.variables['x1'].domain, 'x6':G.variables['x6'].domain})
G.factors['a16^6'] = FactorNode('a16^6', f166, ring)
G.connect('a16^1', 'x1')
G.connect('a16^1', 'x6', True)
G.connect('a16^6', 'x6')
G.connect('a16^6', 'x1', True)

running = True
while(running):
    running = False
    for v in list(G.variables.values()) + list(G.factors.values()):
        t = v.get_target()
        if t:
            m = v.extended_message(t)
            print(m)
            v.send(m)
            running = True

assignment = {}
for vn in G.variables.values():
    assignment[vn.name] = vn.final_assignment()
