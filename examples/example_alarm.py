from __future__ import division
from functools import reduce
import operator

# Import from the parent folder
import sys, os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from pygmalion import *

###########################################
# Operations on Probability Distributions #
###########################################

sum_product = SemiRing(operator.add, 0.0, operator.mul, operator.truediv, 1.0)

def Marginal(P, var):
    return marginalize(P, sum_product, var)

def Joint(P1, P2):
    return join(P1, P2, sum_product)

def Observe(P, **obs):
    return eliminate(P, sum_product, normalize=True, **obs)

def PrintTable(f):
    table = [(", ".join(f.domain), "Value" )]
    for args in iter_product(*[f.domain[x] for x in f.domain.keys()]):
        expanded_args = {k:args[i] for i,k in enumerate(f.domain.keys())}
        table.append((", ".join(map(str, list(args))), str(f(**expanded_args))))
    print(tabulate(table, headers="firstrow"))

#########################
# Example Distributions #
#########################

def P_Dieb(D):
    p = 0.001
    if D == True:
        return p
    else:
        return 1-p
P_Dieb.domain = {'D':[True, False]}

def P_Sturm(S):
    p = 0.01
    if S == True:
        return p
    else:
        return 1-p
P_Sturm.domain = {'S':[True, False]}

def CP_Radio(R,S):
    p = {} # P(R|S)
    p[(True, True)] = 0.9
    p[(False, True)] = 0.1
    p[(True, False)] = 0.1
    p[(False, False)] = 1.0 - 0.1
    return p[(R,S)]
CP_Radio.domain = {'R':[True, False], 'S':[True, False]}

def CP_Alarm(A,D,S):
    p = {} # P(A|D,S)
    p[(True, True, True)] = 0.95
    p[(False, True, True)] = 0.05
    p[(True, True, False)] = 0.9
    p[(False, True, False)] = 0.1
    p[(True, False, True)] = 0.5
    p[(False, False, True)] = 0.5
    p[(True, False, False)] = 0.01
    p[(False, False, False)] = 1-0.01
    return p[(A,D,S)]
CP_Alarm.domain = {'A':[True, False], 'D':[True, False], 'S':[True, False]}

def CP_Wachdienst(W,A):
    p = {} # P(W|A)
    p[(True, True)] = 0.9
    p[(False, True)] = 0.1
    p[(True, False)] = 0.1
    p[(False, False)] = 0.9
    return p[(W,A)]
CP_Wachdienst.domain = {'W':[True, False], 'A':[True, False]}

PrintTable(Joint(CP_Wachdienst,CP_Alarm))