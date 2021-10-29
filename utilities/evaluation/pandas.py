import logging
import xml.etree.ElementTree as ET
import pandas as pd

# def remove_prefix(s, prefix):
#     if s.startswith(prefix):
#         return s[len(prefix):]
#     return s

def process_run(run, file, timeout, solver_override, statistics):
    solver = run.attrib["solver_id"]
    if solver in solver_override:
        solver = solver_override[solver]
    filename = file.attrib["name"]
    # filename = remove_prefix(filename, "QF_NRA/")
    answer = None
    runtime = None
    for res in run.find('./results'):
        if res.get('name') == 'answer':
            answer = res.text
        elif res.get('name') == 'runtime':
            runtime = int(res.text) / 1000.0
        if answer != None and runtime != None:
            break
    if answer == "memout":
        runtime = timeout + 5
    if answer == "timeout":
        runtime = timeout + 10

    result = [None for _ in range(2 + len(statistics))]
    result[0] = answer
    result[1] = runtime

    if statistics != []:
        stats = run.find('./statistics')
        if stats is not None:
            for res in stats:
                if res.get('name') in statistics:
                    result[statistics.index(res.get('name'))+2] = res.text

    return filename,solver,tuple(result)

def xml_to_pandas(filename, solver_override = {}, statistics_filter = None):
    logging.info("Loading %s" % filename)
    tree = ET.parse(filename)
    root = tree.getroot()
    timeout = int(root.find("./information/info[@name='timeout']").get('value'))
    solvers = [s.get('solver_id') for s in root.findall("./solvers/solver")]
    statistics = [s.get('name') for s in root.findall("./statistics/stat")]
    if statistics_filter is not None:
        statistics = [value for value in statistics if value in statistics_filter]

    results = {}
    for file in root.findall('./benchmarks/*'):
        for run in file.findall('./*'):
            idx,solver,res = process_run(run, file, timeout = timeout, solver_override = solver_override, statistics = statistics)
            if not idx in results:
                results[idx] = {}
            results[idx][solver] = res

    print(results)
    # TODO make indizes and stuff

    df = pd.DataFrame(columns = pd.MultiIndex.from_product([solvers, ["answer", "runtime"] + statistics]))
    return df