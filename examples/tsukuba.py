from PIL import Image
from itertools import product as iter_product
from random import *

# Import from the parent folder
import sys, os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))
from pygmalion import *

minsum = SemiRing(max, float('-inf'), operator.add, operator.sub, 0.0)
class MinSumFactorGraph(FactorGraph):
    def __init__(self):
        FactorGraph.__init__(self, minsum)
        
def argmax(f):
    "Find the argmax by brute force"
    ma = None
    mav = float('-inf')
    for args in iter_product(*f.domain.values()):
        expanded_args = {k:args[i] for i,k in enumerate(f.domain.keys())}
        v = f(**expanded_args)
        if v > mav:
            ma, mav = args, v
    return ma[0]

# Resize images to width=100
left = Image.open('tsukuba/left.bmp')
left_data = left.getdata()
right = Image.open('tsukuba/right.bmp')
right_data = right.getdata()
stereo_width, stereo_height = left.size

max_diff = 16

G_stereo = MinSumFactorGraph()
stereo_local_factors = []
stereo_neighbour_factors = []
stereo_neighbours = [] # list of all neighbour pairs
for x in range(stereo_width):
    for y in range(stereo_height):
        if x+1 < stereo_width:
            stereo_neighbours.append(((x,y),(x+1,y)))
        if y+1 < stereo_height:
            stereo_neighbours.append(((x,y),(x,y+1)))

def addNodes():
    def addPixel(x,y):
        name = str(x) + "," + str(y)
        return G_stereo.add_variable(name, range(max_diff))
    
    def color_difference(p1, p2):
        return abs(p1[0]-p2[0])+ abs(p1[1]-p2[1]) + abs(p1[2]-p2[2])

    def addColorMatchFactor(x,y,var):
        diff = max_diff*[None]
        for i in range(max_diff):
            xpos = x-i
            if xpos < 0:
                diff[i] = float('-inf')
            else:
                diff[i] = -color_difference(left_data.getpixel((x,y)), \
                                            right_data.getpixel((xpos,y)))
        def localEnergy(**arg):
            return diff[arg[var.name]]
        localEnergy.domain = {var.name:range(max_diff)}
        return G_stereo.add_factor("colordiff_" + var.name, localEnergy, neighbours = [var])

    def addNeighbourPosFactor(var1, var2):
        def neighbourEnergy(**args):
            return -abs(args[var1.name] - args[var2.name]) * 5
        neighbourEnergy.domain = var1.func.domain.copy()
        neighbourEnergy.domain.update(var2.func.domain)
        return G_stereo.add_factor(var1.name + ":" + var2.name, neighbourEnergy, [var1,var2])

    for x in range(stereo_width):
        for y in range(stereo_height):
            var = addPixel(x,y)
            stereo_local_factors.append(addColorMatchFactor(x,y,var))
    for (x1,y1),(x2,y2) in stereo_neighbours:
        var1 = G_stereo.variables[str(x1) + "," + str(y1)]
        var2 = G_stereo.variables[str(x2) + "," + str(y2)]
        stereo_neighbour_factors.append(addNeighbourPosFactor(var1, var2))

def inference():
    # The local factors send only once
    for lf in stereo_local_factors:
        for n in lf.neighbours:
            G_stereo.send_message(lf, n)

    # All others follow a random schedule
    nodes = list(G_stereo.variables.values()) + stereo_neighbour_factors
    for i in range(4):
        print(i)
        shuffle(nodes)
        for node in nodes:
            for neighbour in node.neighbours:
                G_stereo.send_message(node, neighbour)
    print("done!")

def save():
    depth = Image.new("RGB", left.size)
    depth_data = depth.getdata()
    for x,y in iter_product(range(stereo_width), range(stereo_height)):
        var = G_stereo.variables[str(x) + "," + str(y)]
        value = int(argmax(G_stereo.marginal(var)) * float(255) / float(max_diff-1))
        depth_data.putpixel((x,y), tuple([value,value,value]))
    depth.save("depth5.bmp")

addNodes()
inference()
save()
