import os, sys
import time
import sys
import optparse
import subprocess
import random
import argparse
from Queue import PriorityQueue
import xml.sax
import xml.etree.ElementTree as ET
from xml.sax import saxutils, parse, make_parser, handler
from copy import copy
from itertools import *
import operator
import traci

SUMO_HOME = "C:\\Program Files (x86)\\DLR\\Sumo"
try:
    sys.path.append(os.path.join(SUMO_HOME, "tools"))
    # import the library
    import sumolib
    import unicodedata
    from sumolib import checkBinary
    from sumolib.net import Net
    from sumolib.net import NetReader
    from sumolib.net import Lane
    from sumolib.net import Edge
    from sumolib.net import Node
    from sumolib.net import Connection
    from sumolib.net import Roundabout

except ImportError:
    sys.exit("please declare environment variable 'SUMO_HOME' as the root directory of your sumo installation (it should contain folders 'bin',tools' and 'docs')")

graph = sumolib.net.readNet('test.net.xml')
class priorityDictionary(dict):
    def __init__(self):
        '''Initialize priorityDictionary by creating binary heap
            of pairs (value,key).  Note that changing or removing a dict entry 
            will not remove the old pair from the heap until it is found by smallest() or until the heap is rebuilt.'''
        self.__heap = []
        dict.__init__(self)

    def smallest(self):
        '''Find smallest item after removing deleted items from heap.'''
        if len(self) == 0:
            raise IndexError, "smallest of empty priorityDictionary"
        heap = self.__heap
        while heap[0][1] not in self or self[heap[0][1]] != heap[0][0]:
            lastItem = heap.pop()
            insertionPoint = 0
            while 1:
                smallChild = 2*insertionPoint+1
                if smallChild+1 < len(heap) and \
                        heap[smallChild][0] > heap[smallChild+1][0]:
                    smallChild += 1
                if smallChild >= len(heap) or lastItem <= heap[smallChild]:
                    heap[insertionPoint] = lastItem
                    break
                heap[insertionPoint] = heap[smallChild]
                insertionPoint = smallChild
        return heap[0][1]

    def __iter__(self):
        '''Create destructive sorted iterator of priorityDictionary.'''
        def iterfn():
            while len(self) > 0:
                x = self.smallest()
                yield x
                del self[x]
        return iterfn()

    def __setitem__(self,key,val):
        '''Change value stored in dictionary and add corresponding
            pair to heap.  Rebuilds the heap if the number of deleted items
grows
            too large, to avoid memory leakage.'''
        dict.__setitem__(self,key,val)
        heap = self.__heap
        if len(heap) > 2 * len(self):
            self.__heap = [(v,k) for k,v in self.iteritems()]
            self.__heap.sort()  # builtin sort likely faster than O(n) heapify
        else:
            newPair = (val,key)
            insertionPoint = len(heap)
            heap.append(None)
            while insertionPoint > 0 and val < heap[(insertionPoint-1)//2][0]:
                heap[insertionPoint] = heap[(insertionPoint-1)//2]
                insertionPoint = (insertionPoint-1)//2
            heap[insertionPoint] = newPair

    def setdefault(self,key,val):
        '''Reimplement setdefault to call our customized __setitem__.'''
        if key not in self:
            self[key] = val
        return self[key]

    def update(self, other):
        for key in other.keys():
            self[key] = other[key]

def Dijkstra(graph, start, end=None):
    D = {}    # dictionary of final distances
    P = {}    # dictionary of predecessors
    Q = priorityDictionary()    # estimated distances of non-final vertices
    Q[start] = 0
    edge = graph.getEdges()
    for vertex in Q:
        D[vertex] = Q[vertex]
        if vertex == end: break
        for edge in vertex.getOutgoing():
            vwLength = D[vertex] + edge.getLength()
            if edge not in D and (edge not in Q or vwLength < Q[edge]):
                Q[edge] = vwLength
                P[edge] = vertex
    return (D,P)

def Dijkstra_with_congestion(graph, start, end=None):
    ## congestion at 0 is max and congestion at 1 is min
    D = {}    # dictionary of final distances
    P = {}    # dictionary of predecessors
    Q = priorityDictionary()    # estimated distances of non-final vertices
    Q[start] = 0
    edge = graph.getEdges()
    congestion = getCongestion('test.taz.xml')
    for vertex in Q:
        D[vertex] = Q[vertex]
        if vertex == end: break
        for key, value in congestion:
            for edge in vertex.getOutgoing():
                vwLength = (D[vertex] + edge.getLength()) * (1 - value[0])
                if edge in D:
                    if vwLength < D[edge]:
                        return Dijkstra(graph,start,end)
                        #"Dijkstra: same as Dijkstras without weights"
                elif edge not in Q or vwLength < Q[edge]:
                    Q[edge] = vwLength
                    P[edge] = vertex
    return (D,P)

def Dijkstra_with_overheads(graph, start, end=None):
    ## congestion at 0 is max and congestion at 1 is min
    D = {}    # dictionary of final distances
    P = {}    # dictionary of predecessors
    Q = priorityDictionary()    # estimated distances of non-final vertices
    Q[start] = 0
    edge = graph.getEdges()
    overheads = getOverheads('test.taz.xml')
    for vertex in Q:
        D[vertex] = Q[vertex]
        if vertex == end: break
        for key, value in overheads:
            for edge in vertex.getOutgoing():
                vwLength = (D[vertex] + edge.getLength()) * (1 - value[0])
                if edge in D:
                    if vwLength < D[edge]:
                        return Dijkstra(graph,start,end)
                        #"Dijkstra: same as Dijkstras without weights"
                elif edge not in Q or vwLength < Q[edge]:
                    Q[edge] = vwLength
                    P[edge] = vertex
    return (D,P)

def generate_routefile(route):
    with open("dijk1.rou.xml", "w") as routes:
        routes.write('<routes> \n')
        ## Creating 100 vehicles for simulation
        for i in range(100):
            routes.write('<vType id=\"vehicle'+str(i)+'\" accel=\"0.8\" decel=\"4.5\" sigma=\"0.5\" length=\"5\" minGap=\"2.5\" maxSpeed=\"16.67\" guiShape=\"passenger\" /> \n')
            routes.write('<vehicle id =\"'+str(i)+'\" depart=\"'+str(0.5+i)+'\" departLane=\"free\" departSpeed=\"max\"> \n')
            routes.write('<route id=\"'+str(i)+'\" edges=\"'+route+'\" /> \n')
            routes.write('</vehicle> \n')
        routes.write('</routes>')

def getOverheads(filename):
    congestion = dict()
    tree = ET.parse(filename)
    root = tree.getroot()
    for additional in root:
        for tazs in additional:
            congestion[int(tazs.get('id'))] = []
            congestion[int(tazs.get('id'))].append(float(tazs.get('overheads')))
            congestion[int(tazs.get('id'))].append(str(tazs.get('edges')))
    congestion = sorted(congestion.items(), key=operator.itemgetter(0))
    return congestion

def getCongestion(filename):
    congestion = dict()
    tree = ET.parse(filename)
    root = tree.getroot()
    for additional in root:
        for tazs in additional:
            congestion[int(tazs.get('id'))] = []
            congestion[int(tazs.get('id'))].append(float(tazs.get('congestion')))
            congestion[int(tazs.get('id'))].append(str(tazs.get('edges')))
    congestion = sorted(congestion.items(), key=operator.itemgetter(0))
    return congestion

def shortestPath(graph, start, end, arg):
    """
    Find a single shortest path from the given start vertex to the given
end vertex.
    The input has the same conventions as Dijkstra().
    The output is a list of the vertices in order along the shortest path.
    """
    start = graph.getEdge(start)
    end = graph.getEdge(end)
    if arg == 0:
        start_time = time.time() ## Starting time calculation
        D,P = Dijkstra(graph, start, end)
        end_time = time.time() ## Ending time calculation
        elapsed_time = (end_time - start_time) ## Calculating the total time in the process
        print("Total time taken : " + str(elapsed_time))
    elif arg == 1:
        start_time = time.time() ## Starting time calculation
        D,P = Dijkstra_with_congestion(graph, start, end)
        end_time = time.time() ## Ending time calculation
        elapsed_time = (end_time - start_time) ## Calculating the total time in the process
        print("Total time taken : " + str(elapsed_time))
    else:
        start_time = time.time() ## Starting time calculation
        D,P = Dijkstra_with_overheads(graph, start, end)
        end_time = time.time() ## Ending time calculation
        elapsed_time = (end_time - start_time) ## Calculating the total time in the process
        print("Total time taken : " + str(elapsed_time))
    Path = []
    while 1:
        Path.append(end)
        if end == start: break
        end = P[end]
    Path.reverse()
    return Path

def main(route):
    edges = [edge.getID() for edge in route]
    string = ""
    for data in edges:
        string += unicodedata.normalize('NFKD', data).encode('ascii','ignore') + " "
    generate_routefile(string)

def initOptions():
    argParser = argparse.ArgumentParser()
    argParser.add_argument("-r", "--routing_algorithm", default="dijkstra", type=str, help="select the routing algorithm")
    argParser.add_argument("--nogui", action="store_true", default=False, help="run the commandline version of sumo")
    args = argParser.parse_args()
    return args

# this is the main entry point of this script
if __name__ == "__main__":
    options = initOptions()
    # this script has been called from the command line. It will start sumo as a
    # server, then connect and run
    if options.nogui:
       sumoBinary = checkBinary('sumo')
    else:
       sumoBinary = checkBinary('sumo-gui')

    if options.routing_algorithm == "dijkstra-with-congestion":
        route = shortestPath(graph, '-422766323#3', '-193223413#2', 1)
    elif options.routing_algorithm == "dijkstra":
        route = shortestPath(graph, '-422766323#3', '-193223413#2', 0)
    else:
        route = shortestPath(graph, '-422766323#3', '-193223413#2', 2)
    # this is the normal way of using traci. sumo is started as a
    # subprocess and then the python script connects and runs
    sumoProcess = subprocess.Popen([sumoBinary, "-c", "dijkstra.sumocfg"])
    main(route)
    sumoProcess.wait()