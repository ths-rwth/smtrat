import pandas as pd
import matplotlib.pyplot as plt

def filter_solved(df, solver):
    return df.loc[df[(solver,'answer')].isin(['sat','unsat'])].copy()

def cumulate_by_column(df, column):
    df.loc[:,'num'] = 1
    df = df.groupby([column]).count()
    df.loc[:,'num'] = df["num"].cumsum()
    df = df[['num']]
    df = df.reset_index().set_index('num')
    return df

def performance_profile(df, solvers, column = 'runtime'):
    ax = plt.gca()
    for solver in solvers:
        cumulate_by_column(filter_solved(df, solver), (solver, column)).plot.line(ax=ax)
    ax.set_ylabel(column)
    ax.set_xlabel("number of solved instances")
    return ax

def virtual_best(df, solvers, name, statistics=[]):
    data = []
    for _, row in df.iterrows():
        s = solvers[0]
        for solver in solvers:
            if row[(solver,'runtime')] < row[(s,'runtime')]:
                s = solver
        new_row = []
        new_row.append(row[(s,'answer')])
        new_row.append(row[(s,'runtime')])
        for stat in statistics:
            if stat in row[s]:
                new_row.append(row[(s,stat)])
            else:
                new_row.append(None)

        data.append(tuple(new_row))
    columns = ['answer','runtime'] + statistics
    return pd.DataFrame(data, df.index, columns=pd.MultiIndex.from_product([[name], columns]))