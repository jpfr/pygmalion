import copy
import operator
import math
from itertools import product as iter_product
from functools import reduce
from tabulate import tabulate

##########################
# Introspected Functions #
##########################

class SemiRing(object):
    """"
    A commutative semiring. Inverse multiplication can be set to None if not
    available. Then, variable elimination (adding evidence) will be
    unnormalized.
    """
    def __init__(self, add, zero, mul, invmul, one):
        self.add = add
        self.zero = zero
        self.mul = mul
        self.invmul = invmul
        self.one = one

def unity(ring, domain={}):
    """
    Create a function that returns the ring's multiplicative
    identity for any argument
    """
    def u(**args):
        return ring.one
    u.domain = domain
    return u

def marginalize_out(f, ring, var):
    """
    Marginalize out the given variable according to the addition
    operator of the ring and the domain of the variable
    """
    marginalized_domain = {k:v for k,v in f.domain.items() if k is not var}
    results = {}
    for args in iter_product(*marginalized_domain.values()):
        expanded_args = {k:args[i] for i,k in enumerate(marginalized_domain.keys())}
        total = ring.zero
        for val in f.domain[var]:
            expanded_args[var] = val
            total = ring.add(total, f(**expanded_args))
        results[args] = total
    def marginalized(**args):
        t = tuple(args[var] for var in marginalized_domain.keys())
        return results[t]
    marginalized.domain = marginalized_domain
    return marginalized

def marginalize(f, ring, keep_var):
    """
    Marginalize out all variables that are not (in) keep_var.
    """
    if not type(keep_var) == list:
        keep_var = [keep_var]
    new_func = f
    for arg in f.domain:
        if not arg in keep_var:
            new_func = marginalize_out(new_func, ring, arg)
    return new_func

def join(f1, f2, ring):
    """
    The functions are merged using the ring's multiplication operator.
    The new domain is the union of the original domains.
    """
    joined_domain = f1.domain.copy()
    joined_domain.update(f2.domain.items())
    results = {}
    arg_list_total = list(joined_domain.keys())
    for args in iter_product(*joined_domain.values()):
        expanded_args1 = {k:args[i] for i,k in enumerate(joined_domain) if k in f1.domain}
        expanded_args2 = {k:args[i] for i,k in enumerate(joined_domain) if k in f2.domain}
        results[args] = ring.mul(f1(**expanded_args1), f2(**expanded_args2))
    def joined(**args):
        t = tuple(args[var] for var in joined_domain.keys())
        return results[t]
    joined.domain = joined_domain
    return joined

def eliminate(f, ring, normalize=False, **elim):
    """
    Fix the given variables to a fixed value. The resuling function
    can be normalized if an inverse multiplication operator is available.
    """
    if normalize:
        var_only = marginalize(f, ring, list(elim.keys()))
        normalization_constant = var_only(**elim)
    def eliminated(**args):
        args.update(elim)
        result = f(**args)
        if normalize:
            return ring.invmul(result, normalization_constant)
        else:
            return result
    eliminated.domain = {k:f.domain[k] for k in f.domain.keys() if k not in elim}
    return eliminated

def normalize(f, ring, amount=None):
    """
    If amount is not set, then we normalize by inverse multiplication
    (according to the ring) by the sum of all function values.
    """
    if amount == None:
        amount = ring.zero
        for args in iter_product(*f.domain.values()):
            expanded_args = {k:args[i] for i,k in enumerate(f.domain.keys())}
            amount = ring.add(amount, f(**expanded_args))
    def normalized(**args):
        return ring.invmul(f(**args), amount)
    normalized.domain = f.domain
    return normalized

def print_func(f):
    table = [(", ".join(f.domain), "Value" )]
    for args in iter_product(*f.domain.values()):
        expanded_args = {k:args[i] for i,k in enumerate(f.domain.keys())}
        table.append((", ".join(map(str, list(args))), str(f(**expanded_args))))
    print(tabulate(table, headers="firstrow"))

################
# Factor Graph #
################

class Node(object):
    def __init__(self, name, func):
        self.name = name
        self.func = func # for variable nodes, func is the multiplicative unity
        self.neighbours = []
        self.received_messages = {} # maps neighbour-names to messages

class VariableNode(Node):
    pass

class FactorNode(Node):
    pass

class FactorGraph(object):
    def __init__(self, ring, variables={}, factors={}):
        self.ring = ring
        self.variables = variables
        self.factors = factors

    def add_variable(self, name, domain, neighbours=[]):
        func = unity(self.ring, {name:domain})
        vn = VariableNode(name, func)
        self.variables[name] = vn
        vn.neighbours += neighbours
        for n in neighbours:
            n.neighbours.append(vn)
        return vn

    def add_factor(self, name, func, neighbours=[]):
        fn = FactorNode(name, func)
        self.factors[name] = fn
        fn.neighbours += neighbours
        for n in neighbours:
            n.neighbours.append(fn)
        return fn

    def message(self, source, target):
        f = source.func # unity if source is a variable node
        for neighbour, m in source.received_messages.items():
            if neighbour == target.name:
                continue
            f = join(f, m, self.ring)
        message_domain = target.name if type(source) == FactorNode else source.name
        return marginalize(f, self.ring, message_domain)
        ## Normalize the message
        # first_arg = {k:f.domain[k][0] for k in f.domain.keys()}
        # invkappa = f(**first_arg)
        # return normalize(f, self.ring, invkappa)

    def send_message(self, source, target):
        m = self.message(source, target)
        target.received_messages[source.name] = m

    def marginal(self, node):
        f = node.func
        for m in node.received_messages.values():
            f = join(f, m, self.ring)
        return marginalize(f, self.ring, node.name)
