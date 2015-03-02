import copy
import operator
import math
from collections import OrderedDict
from itertools import product as iter_product
from functools import reduce
from tabulate import tabulate

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
    "Create a function that returns the ring's multiplicative identity for any argument"
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
    new_domain.update(f2.domain.items())
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

def normalize(f, ring, amount=None):
    "If amount is not set, then we normalize by inverse multiplication \
    (according to the ring) by the sum of all function values."
    if amount == None:
        amount = ring.zero
        for args in iter_product(*[f.domain[x] for x in arguments(f)]):
            amount = ring.add(amount, f(*args))
    def normalized(*args):
        return ring.invmul(f(*args), amount)
    normalized.domain = f.domain
    return normalized

def print_func_table(f):
    table = [( ("(" + ", ".join(arguments(f)) + ")", "value") )]
    for args in iter_product(*[f.domain[x] for x in arguments(f)]):
        table.append( (str(args), str(f(*args))) )
    print(tabulate(table, headers="firstrow"))

################
# Factor Graph #
################

class Message(object):
    def __init__(self, source, destination, func, time=0, variableinfos = {}):
        self.source = source
        self.destination = destination
        self.func = func
        self.time = time
        self.variableinfos = variableinfos # used in the remote neighbour extension

    def __repr__(self):
        return "<Message: %s -> %s,\tDomain: [%s],\tVariableInfos: [%s]>" % \
            (self.source.name, self.destination.name, ",".join(self.func.domain.keys()), \
             ",".join(self.variableinfos.keys()))

class Node(object):
    def __init__(self, name, func, ring, neighbours=[], remote_neighbours=[]):
        self.name = name
        self.func = func # if the node is a variable, func is unity (with the right domain)
        self.ring = ring
        self.neighbours = neighbours[:]
        self.remote_neighbours = remote_neighbours[:] # for the remote neighbours extension
        self.received_messages = {}
        self.last_send = {} # the last time a message was sent to a given neighbour

    def message_target(self):
        "A node can only send to a neighbour if it has not already sent to that \
        neighbour and it has received messages from all other neighbours."
        possible_targets = dict((n, len(self.neighbours)) for n in self.neighbours)
        for received_from in self.received_messages.keys():
            for target in possible_targets:
                if received_from != target.name:
                    possible_targets[target] -= 1
        for pt, count in possible_targets.items():
            if count == 1 and not self.name in pt.received_messages:
                return pt
        return None

    def send(self, message):
        recipient = message.destination
        self.last_send[recipient.name] = message.time
        recipient.received_messages[self.name] = message
        return message

    def send_if_update(self, message):
        "Send the message only if it is not equal to the message that was sent before"
        recipient = message.destination
        self.last_send[recipient.name] = message.time
        if not self.name in recipient.received_messages:
            recipient.received_messages[self.name] = message
            return message
        old_message = recipient.received_messages[self.name]
        epsilon = 0.0001
        for args in iter_product(*[dom for dom in message.func.domain.values()]):
            if math.fabs(old_message.func(*args) - message.func(*args)) > epsilon:
                recipient.received_messages[self.name] = message
                return message
        return None

    def marginal(self):
        f = self.func
        for m in self.received_messages.values():
            f = merge(f, m.func, self.ring)
        f = marginalize_others(f, self.ring, self.name)
        return f

    def reset(self):
        self.received_messages = {}

class VariableNode(Node):
    def __init__(self, name, domain, ring, neighbours=[], remote_neighbours=[]):
        self.domain = domain
        func = unity(ring, OrderedDict([(name, domain)]))
        super(VariableNode, self).__init__(name, func, ring, neighbours, remote_neighbours)

class FactorNode(Node):
    def __init__(self, name, func, ring, neighbours=[], remote_neighbours=[]):
        super(FactorNode, self).__init__(name, func, ring, neighbours, remote_neighbours)

def create_timer():
    "A (non wall-time) timer that returns a monotonically increasing value. \
    Can also be used to count the sent message (globally)."
    thistime = [0] # lists can be accessed from within a closure, but not scalars
    def timer():
        thistime[0] += 1
        return thistime[0]
    return timer

class FactorGraph(object):
    def __init__(self, ring, variables={}, factors={}):
        self.ring = ring
        self.variables = variables
        self.factors = factors
        self.time = create_timer()

    def addVariableNode(self, name, domain, neighbours=[], remote_neighbours=[]):
        vn = VariableNode(name, domain, self.ring)
        self.variables[name] = vn
        self.connect(vn, neighbours)
        self.connect(vn, remote_neighbours, True)
        return vn

    def addFactorNode(self, name, func, neighbours=[], remote_neighbours=[]):
        fn = FactorNode(name, func, self.ring)
        self.factors[name] = fn
        self.connect(fn, neighbours)
        self.connect(fn, remote_neighbours, True)
        return fn

    def connect(self, a, b, remote=False):
        "Make an edge between two nodes or between a source and several neighbours."
        if not type(b) == list:
            b = [b]
        for b_ in b:
            if remote:
                a.remote_neighbours.append(b_)
                b_.remote_neighbours.append(a)
            else:
                a.neighbours.append(b_)
                b_.neighbours.append(a)

    def reset(self):
        for vn in self.variables.values():
            vn.reset()
        for fn in self.factors.values():
            fn.reset()    

    def message(self, source, target):
        f = source.func
        for neighbour, m in source.received_messages.items():
            if neighbour == target.name:
                continue
            f = merge(f, m.func, self.ring)
        message_domain = target.name if type(source) == FactorNode else source.name
        f = marginalize_others(f, self.ring, message_domain)
        first_arg = tuple([f.domain[d][0] for d in f.domain.keys()])
        invkappa = f(*first_arg)
        f = normalize(f, self.ring, invkappa)
        return Message(source, target, f, self.time())

    def merge_factors(self):
        return reduce(lambda f1, f2: merge(f1, f2, self.ring), \
                      [fn.func for fn in self.factors.values()])

##############################
# Remote Neighbour Extension #
##############################

class VariableInfo(object):
    def __init__(self, name, neighbourcount, visitcount):
        self.name = name
        self.neighbourcount = neighbourcount # neighbours + remote neighbours
        self.visitcount = visitcount # how many of the neighbours did the message visit?

def updated_variableinfos(source, target):
    vis = {}
    for sender, m in source.received_messages.items():
        if sender == target.name:
            continue
        for vi in m.variableinfos.values():
            if vi.name in vis:
                vis[vi.name].visitcount += vi.visitcount
            else:
                vis[vi.name] = copy.deepcopy(vi)
    if source.name in vis:
        vis[source.name].visitcount += 1
    elif type(source) == VariableNode:
        vis[source.name] = VariableInfo(source.name, len(source.remote_neighbours) + \
                                        len(source.neighbours) + 1, 1)
    for n in source.remote_neighbours + source.neighbours:
        if n.name in vis:
            vis[n.name].visitcount += 1
        elif type(source) == FactorNode:
            vis[n.name] = VariableInfo(n.name, len(n.remote_neighbours) + \
                                       len(n.neighbours) + 1, 1)
    return dict(filter(lambda x: x[1].neighbourcount > x[1].visitcount, vis.items()))

def extended_message(source, target, ring, time):
    f = source.func
    for node, m in source.received_messages.items():
        if node == target.name:
            continue
        f = merge(f, m.func, ring)
    variableinfos = updated_variableinfos(source, target)
    f = marginalize_others(f, ring, variableinfos.keys())
    return Message(source, target, f, time, variableinfos)

