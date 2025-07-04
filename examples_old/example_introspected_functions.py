from pygmalion import *

def func1(x1, x2):
    return x1 * x2
func1.domain = OrderedDict([('x1',[1,2,3]), ('x2',[1,2,3])])

def func2(x2, x3):
    return x2 * x3
func2.domain = OrderedDict([('x2',[1,2,3]), ('x3',[1,2,3])])

ring = Ring(operator.add, 0, operator.mul, operator.truediv, 1) # plus-mul
c = merge(func1, func2, ring)
m = marginalize(c, ring, 'x2')
e = eliminate(c, ring, 'x3', 1)

print("## Examples for the introspected functions ##")
print(c(1,2,3))
print(m(2,3))
print(arguments(m))
print(m.domain)
print_func_table(m)
