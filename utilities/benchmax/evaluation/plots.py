from .data import *
import matplotlib.pyplot as plt
import numpy as np
from PIL import Image
import tikzplotlib

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
            df[df[category] == cat].plot.scatter(ax = ax, x=(solver1, field), y=(solver2, field), label=cat, c=colormap[cat], alpha=0.5)
    else:
        df.plot.scatter(ax = ax, x=(solver1, field), y=(solver2, field), alpha=0.5)
    ax.set_xlabel(solver1)
    ax.set_ylabel(solver2)
    return ax

def scatter_equal_line(ax):
    lower = max(ax.get_xlim()[0],ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1],ax.get_ylim()[1])
    ax.plot([lower, upper], [lower, upper], ls="--", c=".3")

def save_scatter(ax, file, size):
    low_x = ax.get_xlim()[0]
    up_x = ax.get_xlim()[1]
    low_y = ax.get_ylim()[0]
    up_y = ax.get_ylim()[1]
    lower = max(ax.get_xlim()[0],ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1],ax.get_ylim()[1])
    ax.plot(lower, lower, 'o',c='black',ms=1)
    ax.plot(upper, upper, 'o',c='black',ms=1)
    ax.set_axis_off()
    plt.savefig(file+".png")

    def bbox(im):
        a = np.array(im)[:,:,:3]  # keep RGB only
        m = np.any(a != [255, 255, 255], axis=2)
        coords = np.argwhere(m)
        y0, x0, y1, x1 = *np.min(coords, axis=0), *np.max(coords, axis=0)
        return (x0, y0, x1+1, y1+1)

    im = Image.open(file+".png")
    im2 = im.crop(bbox(im))
    im2.save(file+".png")

    for el in plt.gca().lines + plt.gca().collections:
        el.remove()

    ax.set_xlim(low_x,up_x)
    ax.set_ylim(low_y,up_y)
    ax.plot([lower, upper], [lower, upper], ls="--", c=".3")

    ax.set_axis_on()
    tikzplotlib.save(file)

    with open(file, 'r') as f:
        content = f.read()

    idx = content.index("\\begin{axis}")
    content = content[:idx] + "\\node[inner sep=0pt,anchor=south west] at (0,0) {\includegraphics[width="+str(size)+"cm]{"+file+".png}};\n" + content[idx:]

    idx = content.index("\\begin{axis}[") + len("\\begin{axis}[")
    content = content[:idx] + "\nwidth="+str(size)+"cm, height="+str(size)+"cm, scale only axis, at={(0,0)}," + content[idx:]

    with open(file, 'w') as f:
        f.write(content)