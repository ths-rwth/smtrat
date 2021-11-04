import pandas as pd
from .data import *

def inspect_answer(df):
    solvers = get_solvers(df)
    answers = ['sat','unsat','unknown','wrong','error','timeout','memout','no answer','segmentation fault','segfault','abort']
    
    data = []
    data.append(tuple([len(df) for _ in solvers]))
    for answer in answers:
        r = []
        for solver in solvers:
            vc = df[(solver,'answer')].value_counts()
            if answer in vc:
                r.append(vc[answer])
            else:
                r.append(0)
        data.append(tuple(r))

    data.append(tuple([data[1][i] + data[2][i] for i in range(len(solvers))]))

    return pd.DataFrame(data,index = ['count'] + answers + ['solved'], columns=solvers)

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