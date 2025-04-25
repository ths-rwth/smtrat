# convert https://researchdata.bath.ac.uk/69/ to smtlib

import requests
from smtlib_from_qepcad import to_smtlib
import os

url = 'https://researchdata.bath.ac.uk/69/3/QEPCADexamplebank_v4.txt'
data = requests.get(url).text

out_dir = "/home/jnalbach/vc/smt/benchmarks/NRA-quantifier-elimination/david-wilson/"

category = None
instance = None
flag = False

num_formulas = 0
num_instances = 0

if not os.path.isdir(out_dir):
    os.mkdir(out_dir)


for line in data.splitlines()[9:]:
    if line.startswith("#==================================================="):
        category = None
        assert(instance == None)
    elif line.startswith("# ") and category == None:
        category = line[2:].replace(" ","_")
        assert(instance == None)
    elif line.startswith("#") and not line.startswith("# ") and not line.startswith("#==================================================="):
        assert(instance == None)
        instance = line[1:].replace(" ","_").replace(":","").replace("\\",'').replace("'",'').replace("(",'').replace(")",'')
        flag = False
        num_instances = num_instances + 1
    elif line.startswith('(E') or line.startswith('(A') or (line.startswith('[') and flag):
        assert(category != None and instance != None)
        num_formulas = num_formulas + 1
        assert(line.endswith("."))
        formula = line[0:-1]
        print(category, instance, formula)
        if not os.path.isdir(out_dir + "/" + category):
            os.mkdir(out_dir + "/" + category)
        output = to_smtlib(formula)
        with open(out_dir + "/" + category + "/" + instance + ".smt2", 'w') as f:
            f.write(output)
        instance = None
    elif line.startswith('['):
        assert(category != None and instance != None)
        flag = True

assert(num_formulas == num_instances)