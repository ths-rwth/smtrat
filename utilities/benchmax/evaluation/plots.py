from .data import *
import matplotlib.pyplot as plt

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

