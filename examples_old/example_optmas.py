from pygmalion import *
from random import random, randint, seed

# config
s = 9
seed(s)
remote_neighbour_extension = True

ring = Ring(max, float('-inf'), operator.add, operator.sub, 0) # max-plus

def find_max(f):
    "Find the argmax on the entire domain of the function by brute force"
    args = arguments(f)
    ma = None
    mav = float('-inf')
    for x in iter_product(*[f.domain[x] for x in args]):
        v = f(*x)
        if v > mav:
            ma, mav = x, v
    return {list(f.domain.keys())[i]:ma[i] for i in range(len(args))}

def max_assignment(vn):
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
x1 = G.addVariableNode('x1', range(5))
x2 = G.addVariableNode('x2', range(5))
x3 = G.addVariableNode('x3', range(5))
x4 = G.addVariableNode('x4', range(5))
x5 = G.addVariableNode('x5', range(5))
x6 = G.addVariableNode('x6', range(5))
x7 = G.addVariableNode('x7', range(5))
x8 = G.addVariableNode('x8', range(5))
f12 = create_random_func([x1, x2])
f23 = create_random_func([x2, x3])
f34 = create_random_func([x3, x4])
f144 = create_random_func([x1, x4])
f458 = create_random_func([x4, x5, x8])
f56 = create_random_func([x5, x6])
f67 = create_random_func([x6, x7])
f78 = create_random_func([x7, x8])
a12 = G.addFactorNode('a12', f12, [x1, x2])
a23 = G.addFactorNode('a23', f23, [x2, x3])
a34 = G.addFactorNode('a34', f34, [x3, x4])
if remote_neighbour_extension:
    a144 = G.addFactorNode('a14^4', f144, x4, x1)
    a458 = G.addFactorNode('a458^{45}', f458, [x4, x5], x8)
else: # loopy
    a144 = G.addFactorNode('a14^4', f144, [x4, x1])
    a458 = G.addFactorNode('a458', f458, [x4, x5, x8])
a56 = G.addFactorNode('a56', f56, [x5, x6])
a67 = G.addFactorNode('a67', f67, [x6, x7])
a78 = G.addFactorNode('a78', f78, [x7, x8])

if remote_neighbour_extension:
    running = True
    while(running):
        running = False
        for n in list(G.variables.values()) + list(G.factors.values()):
            t = n.message_target()
            if t:
                m = n.send(extended_message(n, t, G.ring, G.time()))
                print(m)
                running = True
    assignment = {}
    for vn in G.variables.values():
        assignment[vn.name] = max_assignment(vn)
else: # loopy .. with output into file for graphing
    all_nodes = G.variables.values() + G.factors.values()
    i = 0
    # c = 0
    # f = open('results'+str(s)+'.dat','w')
    while i < 5000:
        for n in all_nodes:
            i = i+1
            for t in n.neighbours:
                m = n.send_if_update(G.message(n, t))
    ## file output for graphing
    #             if not m:
    #                 continue
    #             c = c+1
    #             assignment = {}
    #             for vn in G.variables.values():
    #                 assignment[vn.name] = max_assignment(vn)
    #             total = ring.one
    #             for fn in G.factors.values():
    #                 args = list(fn.func.domain.keys())
    #                 for x in range(len(args)):
    #                     args[x] = assignment[args[x]]
    #                 total = ring.mul(total, fn.func(*args))
    #             f.write(str(c) + " " + str(total) + "\n")
    # while c < 1000:
    #     c = c+1
    #     f.write(str(c) + " " + str(total) + "\n")
    # f.close()
    assignment = {}
    for vn in G.variables.values():
        assignment[vn.name] = max_assignment(vn)

print("Max assignment found with message passing:")
print(assignment)
total = 0
for fn in G.factors.values():
    args = list(fn.func.domain.keys())
    for x in range(len(args)):
        args[x] = assignment[args[x]]
    total = ring.mul(total, fn.func(*args))
print("Total: " + str(total))

# Brute force for comparison
print("Max assignment found by brute force")
print("...computing...")
single_factor = G.merge_factors()
assignment = find_max(single_factor)
args = list(single_factor.domain.keys())
for x in range(len(args)):
    args[x] = assignment[args[x]]
print(single_factor(*args))
