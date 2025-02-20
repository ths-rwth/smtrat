import logging
import xml.etree.ElementTree as ET
import pandas as pd


# auxiliary method used by xml_to_pandas
def process_run(run, file, timeout, statistics):
    solver = run.attrib["solver_id"]
    filename = file.attrib["name"]
    answer = None
    runtime = None
    mem = None
    for res in run.find("./results"):
        if res.get("name") == "answer":
            answer = res.text
        elif res.get("name") == "runtime":
            runtime = int(res.text)
        elif res.get("name") == "peak_memory":
            mem = int(res.text)
        if answer != None and runtime != None and mem != None:
            break
    if answer == "memout":
        runtime = timeout + 5
    if answer == "timeout":
        runtime = timeout + 10

    result = [None for _ in range(3 + len(statistics))]
    result[0] = answer
    result[1] = runtime
    result[2] = mem

    if statistics != []:
        stats = run.find("./statistics")
        if stats is not None:
            for res in stats:
                if res.get("name") in statistics:
                    result[statistics.index(res.get("name")) + 3] = res.text

    return filename, solver, tuple(result)


def xml_to_pandas(filename, solver_override={}, statistics_filter=None):
    logging.info("Loading %s" % filename)
    tree = ET.parse(filename)
    root = tree.getroot()
    timeout = int(root.find("./information/info[@name='timeout']").get("value"))
    solvers = [s.get("solver_id") for s in root.findall("./solvers/solver")]
    statistics = [s.get("name") for s in root.findall("./statistics/stat")]
    if statistics_filter is not None:
        statistics = [value for value in statistics if value in statistics_filter]

    results = {}
    for file in root.findall("./benchmarks/*"):
        for run in file.findall("./*"):
            filename, solver, res = process_run(
                run, file, timeout=timeout, statistics=statistics
            )
            if not filename in results:
                results[filename] = {}
            results[filename][solver] = res

    data = []
    index = []
    empty = [None for _ in range(0, 2 + len(statistics))]
    for filename in results:
        index.append(filename)
        row = []
        for solver in solvers:
            if solver in results[filename].keys():
                row.extend(list(results[filename][solver]))
            else:
                row.extend(empty)
        data.append(tuple(row))

    df = pd.DataFrame(
        data,
        index,
        columns=pd.MultiIndex.from_product(
            [
                map((lambda s: solver_override.get(s, s)), solvers),
                ["answer", "runtime", "peak_memory_kbytes"] + statistics,
            ]
        ),
    )
    return df


def xmls_to_pandas(params, statistics_filter=None):
    df = None
    for filename in params:
        if df is None:
            df = xml_to_pandas(filename, params[filename], statistics_filter)
        else:
            df = df.join(xml_to_pandas(filename, params[filename], statistics_filter))
    return df


def transform_to_seconds(df):
    for solver in df.columns.get_level_values(0).unique():
        df[(solver, "runtime")] /= 1000


def filter_solvers(df, only=None, exclude=None):
    if only:
        df = df[[c for c in df.columns if c[0] in only]]
    if exclude:
        df = df[[c for c in df.columns if not c[0] in exclude]]
    return df


def rename_solvers(df, name_map: dict[str, str]):
    df.columns = df.columns.set_levels(
        map(lambda x: name_map.get(x, x), df.columns.levels[0]), level=0
    )
    return df


def csv_to_pandas(filename, only=None, exclude=None, rename={}):
    df = pd.read_csv(filename, header=[0, 1], index_col=0)
    df = filter_solvers(df, only, exclude)
    df = rename_solvers(df, rename)
    # transform_to_seconds(df)
    return df
