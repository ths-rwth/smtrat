import pandas as pd
from .data import *

def inspect_answer(df, avg_runtimes = False):
    solvers = get_solvers(df)
    answers = ['sat','unsat','unknown','wrong','error','timeout','memout','no answer','segmentation fault','segfault','abort','invalid']
    
    data = []

    if avg_runtimes:
        r = []
        for solver in solvers:
            r.append(len(df[~df[(solver,'answer')].isnull()]))
            r.append(df[~df[(solver,'answer')].isnull()][(solver,'runtime')].mean())
        data.append(tuple(r))
    else:
        data.append(tuple([len(df[~df[(solver,'answer')].isnull()]) for solver in solvers])) # count

    for answer in answers:
        r = []
        for solver in solvers:
            vc = df[(solver,'answer')].value_counts()
            if answer in vc:
                r.append(vc[answer])
                if avg_runtimes:
                    r.append(df[df[(solver,'answer')]==answer][(solver,'runtime')].mean())
            else:
                r.append(0)
                if avg_runtimes:
                    r.append(None)
        data.append(tuple(r))

    if avg_runtimes:
        r = []
        for i in range(len(solvers)):
            r.append(data[1][2*i] + data[2][2*i])
            if data[1][2*i] == 0 and data[2][2*i] == 0:
                r.append(None)
            elif data[1][2*i] == 0:
                r.append(data[2][2*i+1])
            elif data[2][2*i] == 0:
                r.append(data[1][2*i+1])
            else:
                r.append((data[1][2*i]*data[1][2*i+1] + data[2][2*i]*data[2][2*i+1]) / (data[1][2*i] + data[2][2*i]))
        data.append(tuple(r))
    else:
        data.append(tuple([data[1][i] + data[2][i] for i in range(len(solvers))])) # solved

    if avg_runtimes:
        columns = [x for a in solvers for x in (a, a+"_avg")]
    else:
        columns = solvers

    return pd.DataFrame(data,index = ['count'] + answers + ['solved'], columns=columns)

def inspect_wrongs(df, solver = None):
    if solver is None and len(get_solvers(df))==1:
        solver = get_solvers(df)[0]
    return df[df[(solver,'answer')] == 'wrong'].sort_values(by=(solver,'runtime'))

def inspect_segfaults(df, solver = None):
    if solver is None and len(get_solvers(df))==1:
        solver = get_solvers(df)[0]
    return df[df[(solver,'answer')] == 'segfault'].sort_values(by=(solver,'runtime'))

def inspect(df):
    ai = inspect_answer(df)
    print(ai)

    for solver in get_solvers(df):
        if ai.loc['wrong',solver] > 0:
            print("\n\n\033[1mThere are wrongs in {}\033[0m".format(solver))
            if (solver,'peak_memory_kbytes') in df.columns:
                i = inspect_wrongs(df, solver)[[(solver,'runtime'),(solver,'peak_memory_kbytes')]]
            else:
                i = inspect_wrongs(df, solver)[[(solver,'runtime')]]
            print(list(i.index))
            print(i)
        if ai.loc['segfault',solver] > 0:
            print("\n\n\033[1mThere are segfaults in {}\033[0m".format(solver))
            if (solver,'peak_memory_kbytes') in df.columns:
                i = inspect_segfaults(df, solver)[[(solver,'runtime'),(solver,'peak_memory_kbytes')]]
            else:
                i = inspect_segfaults(df, solver)[[(solver,'runtime')]]
            print(list(i.index))
            print(i)