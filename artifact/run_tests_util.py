from datetime import timedelta
import re
import subprocess
from timeit import default_timer


def parse_stats(output, stats):
    if stats["exitcode"] == 2:
        stats["answer"] = "sat"
    elif stats["exitcode"] == 3:
        stats["answer"] = "unsat"
    elif stats["exitcode"] == 11:
        stats["answer"] = "timeout"
        return
    elif stats["exitcode"] == 12:
        stats["answer"] = "memout"
        return
    else:
        stats["answer"] = "invalid"
        return    

    # find printed statsitics
    i = output.find("(:")
    if i < 0:
        return

    r_category = re.compile(
        r"\(:(?P<prefix>\S+)\s+\(\s*(?P<values>(?::\S+\s+\S*\s*)+)(?P<tail>\)\s*\)\s*)"
    )
    r_values = re.compile(r":(?P<key>\S+)\s+(?P<val>[^\s):]+)")

    m = re.match(r_category, output[i:])
    while m != None:
        values = re.finditer(r_values, m.group("values"))
        for v in values:
            stat = m.group("prefix") + "_" + v.group("key")
            stats[stat] = v.group("val")
        i += m.end()
        m = re.match(r_category, output[i:])


def call_tool(tool, input_file, print_all_stats=False):
    cmd = "ulimit -S -t 60"            # set the time limit
    cmd += " && ulimit -S -v 4000000"   # set the memory limit
    cmd += " && /usr/bin/time -v"       # use /usr/bin/time to get infos about memory usage
    cmd += " /artifact/tools/" + tool             # add tool variant
    cmd += " " + input_file
    cmd += " --stats.print"

    # time and run command
    start = default_timer()
    res = subprocess.run(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, shell=True
    )
    end = default_timer()

    # gather statistics from output
    stats = {
        "runtime": int(timedelta(seconds=(end - start)).total_seconds()*1000),
        "peak_memory_kbytes": int(re.search(r"Maximum resident set size \(kbytes\): ([0-9]+)", res.stderr).group(1)),
        "exitcode": res.returncode,
    }

    if stats["runtime"] >= 60000:
        stats["answer"] = "timeout"
    elif stats["peak_memory_kbytes"] >= 4000000:
        stats["answer"] = "memout"
    else:
        parse_stats(res.stdout, stats)

    if print_all_stats:
        if input("Show all stats? y/[n] ") == "y":
            print("\n=========================== Showing stats: =====================\n")
            for key, val in stats.items():
                print(f"{key:>30}: {val}")
            print()
    
    return stats
