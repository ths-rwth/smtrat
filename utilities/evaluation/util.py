import pandas as pd
import matplotlib.pyplot as plt

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


def scatter_plot(df, solver1, solver2, field, filter = False, category = None, colormap = {}):
    if filter:
        df = filter_solved(filter_solved(df, solver2), solver1)
    ax = plt.gca()

    if category:
        for cat in df[category].unique():
            df[df[category] == cat].plot.scatter(ax = ax, x=(solver1, field), y=(solver2, field), label=cat, c=colormap[cat])
    else:
        df.plot.scatter(ax = ax, x=(solver1, field), y=(solver2, field))
    ax.set_xlabel(solver1)
    ax.set_ylabel(solver2)
    lower = max(ax.get_xlim()[0],ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1],ax.get_ylim()[1])
    ax.plot([lower, upper], [lower, upper], ls="--", c=".3")
    return ax

