from run_tests_util import *
import pandas as pd
import random
import sys

# Simply comment/uncomment to select the tested tools
tools = [
    "Baseline",
    "Simple-3",
    "Simple-4",
    "Simple-5",
    "Simple-6",
    "Dynamic",
    "Taylor",
    "PWL-2",
    "PWL-4",
    "PWL-6",
    "Outside"
]

number_of_samples = 5
if len(sys.argv) > 1:
    number_of_samples = int(sys.argv[1])

df = pd.read_csv("stats.csv", header=[0,1], index_col=0, low_memory=False)
input_files = random.sample(list(df.index), number_of_samples)

for i in input_files:
    print("===============================================================")
    print(i)
    print("===============================================================")
    print("{:8} | {:8} ({:8}) Time in ms (difference)".format("","Answer","before"))
    print("-"*63)
    for t in tools:
        #collect stats
        stats = call_tool(t, "/artifact/QF_NRA/" + i, print_all_stats=False)
        # validate stats
        row = df.loc[i]
        time_diff = stats["runtime"] - row[(t,"runtime")]
        time_diff_str = "+" + str(time_diff) if time_diff > 0 else str(time_diff)
        print(
            "{:8} | {:8} ({:<8}) {:>5} ({:>6})"
            .format(t,stats["answer"],row[(t,"answer")],stats["runtime"],time_diff_str)
        )
