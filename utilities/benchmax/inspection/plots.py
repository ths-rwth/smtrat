from .data import *
import matplotlib
import matplotlib.pyplot as plt
import numpy as np
from PIL import Image
import tikzplotlib


def setup_accessible_styles():
    linestyles = [
        "-",
        "--",
        ":",
        "-.",
        (5, (10, 3)),
        (0, (5, 10)),
        (0, (5, 5)),
        (0, (5, 1)),
        (0, (3, 5, 1, 5)),
        (0, (3, 1, 1, 1)),
        (0, (3, 5, 1, 5, 1, 5)),
        (0, (3, 1, 1, 1, 1, 1)),
    ]
    colors_blind = [
        "#332288",
        "#117733",
        "#88CCEE",
        "#DDCC77",
        "#CC6677",
        "#AA4499",
        "#882255",
        "#44AA99",
    ]
    colors_rwth = [
        "#00549F",
        "#E30066",
        "#006165",
        "#CC071E",
        "#57AB27",
        "#F6A800",
        "#0098A1",
        "#A11035",
        "#57AB27",
        "#612158",
        "#FFED00",
        "#BDCD00",
    ]
    matplotlib.rcParams["axes.prop_cycle"] = matplotlib.cycler(
        "color", colors_rwth[0:11]
    ) + matplotlib.cycler("linestyle", linestyles[0:11])


def performance_profile(df, solvers, column="runtime"):
    ax = plt.gca()
    for solver in solvers:
        cumulate_by_column(filter_solved(df, solver), (solver, column)).plot.line(ax=ax)
    ax.set_ylabel(column)
    ax.set_xlabel("number of solved instances")
    return ax


def scatter(df, s1, s2, field, ax=None, category=None, colormap={}):
    if ax is None:
        ax = plt.gca()
    if (s1, field + ".active_at_timeout") in df.columns and (
        s2,
        field + ".active_at_timeout",
    ) in df.columns:
        return scatter_timer(df, s1, s2, field, ax, category, colormap)
    else:
        return scatter_field(df, s1, s2, field, ax, category, colormap)


# TODO axis labels bot and top, scatter min and max values
def scatter_field(df, s1, s2, field, ax=None, category=None, colormap={}):
    if ax is None:
        ax = plt.gca()
    df1 = df[[(s1, field), (s2, field)]].copy()

    maxval = max(df[(s1, field)].max(), df[(s2, field)].max()) * 1.05
    df1.loc[(df[(s1, "answer")].isin(["timeout", "memout"])), (s1, field)] = maxval
    df1.loc[(df[(s2, "answer")].isin(["timeout", "memout"])), (s2, field)] = maxval
    #ax.plot([0, maxval*2], [maxval, maxval], ls="-", c=".3")
    #ax.plot([maxval, maxval], [0, maxval*2], ls="-", c=".3")
    ax.plot([0, maxval], [maxval, maxval], ls="-", c=".3")
    ax.plot([maxval, maxval], [0, maxval], ls="-", c=".3")

    # ax.set_xticks(list(ax.get_xticks()) + [maxval], map(str,list(ax.get_xticks()))+ ['$\\bot$'])
    # ax.set_yticks(list(ax.get_yticks()) + [maxval], map(str,list(ax.get_yticks()))+ ['$\\bot$'])

    if category:
        for cat in df[category].unique():
            df1[df1[category] == cat].plot.scatter(
                ax=ax,
                x=(s1, field),
                y=(s2, field),
                label=cat,
                c=colormap[cat],
                alpha=0.5,
            )
    else:
        df1.plot.scatter(ax=ax, x=(s1, field), y=(s2, field), alpha=0.5)

    ax.title.set_text(field)
    ax.set_xlabel(s1)
    ax.set_ylabel(s2)
    return ax


def scatter_timer(df, s1, s2, field, ax=None, category=None, colormap={}):
    if ax is None:
        ax = plt.gca()
    df1 = df[[(s1, field + ".overall_s"), (s2, field + ".overall_s")]].copy()

    maxval = (
        max(df[(s1, field + ".overall_s")].max(), df[(s2, field + ".overall_s")].max())
        * 1.05
    )
    df1.loc[
        (df[(s1, "answer")].isin(["timeout", "memout"])), (s1, field + ".overall_s")
    ] = maxval
    df1.loc[
        (df[(s2, "answer")].isin(["timeout", "memout"])), (s2, field + ".overall_s")
    ] = maxval
    ax.plot([0, maxval], [maxval, maxval], ls="-", c=".3")
    ax.plot([maxval, maxval], [0, maxval], ls="-", c=".3")

    df1.loc[
        (df[(s1, field + ".active_at_timeout")] == 1), (s1, field + ".overall_s")
    ] = (maxval * 1.05)
    df1.loc[
        (df[(s2, field + ".active_at_timeout")] == 1), (s2, field + ".overall_s")
    ] = (maxval * 1.05)
    ax.plot([0, maxval * 1.05], [maxval * 1.05, maxval * 1.05], ls="-", c=".3")
    ax.plot([maxval * 1.05, maxval * 1.05], [0, maxval * 1.05], ls="-", c=".3")

    # ax.set_xticks(list(ax.get_xticks()) + [maxval], map(str,list(ax.get_xticks())) ['$\\bot$'])
    # ax.set_yticks(list(ax.get_yticks()) + [maxval], map(str,list(ax.get_yticks()))+ ['$\\bot$'])
    # ax.set_xticks(list(ax.get_xticks()) + [maxval* 1.05], map(str,list(ax.get_xticks()))+ ['$\\top$'])
    # ax.set_yticks(list(ax.get_yticks()) + [maxval* 1.05], map(str,list(ax.get_yticks()))+ ['$\\top$'])

    if category:
        for cat in df[category].unique():
            df1[df1[category] == cat].plot.scatter(
                ax=ax,
                x=(s1, field + ".overall_s"),
                y=(s2, field + ".overall_s"),
                label=cat,
                c=colormap[cat],
                alpha=0.5,
            )
    else:
        df1.plot.scatter(
            ax=ax, x=(s1, field + ".overall_s"), y=(s2, field + ".overall_s"), alpha=0.5
        )

    ax.title.set_text(field)
    ax.set_xlabel(s1)
    ax.set_ylabel(s2)
    return ax


import math


def scatter_multi(df, s1, s2, fields):
    nrows = math.ceil(len(fields) / 4)
    fig, axs = plt.subplots(nrows=nrows, ncols=4, figsize=(20, 4 * nrows))
    fig.text(0.5, 0.04, s1, ha="center")
    fig.text(0.04, 0.5, s2, va="center", rotation="vertical")

    ax = axs.reshape(-1)

    idx = 0
    for field in fields:
        scatter(df, s1, s2, field, ax[idx])
        ax[idx].set_xlabel(None)
        ax[idx].set_ylabel(None)
        scatter_equal_line(ax[idx])
        idx = idx + 1

    return axs


def scatter_plot(df, solver1, solver2, field, filter=False, category=None, colormap={}):
    if filter:
        df = filter_solved(filter_solved(df, solver2), solver1)
    return scatter(df, solver1, solver2, field, category=category, colormap=colormap)


def scatter_equal_line(ax):
    lower = max(ax.get_xlim()[0], ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1], ax.get_ylim()[1])
    ax.plot([lower, upper], [lower, upper], ls="--", c=".3")


def scatter_axis_equal(ax):
    ax.axis("equal")
    lower = max(ax.get_xlim()[0], ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1], ax.get_ylim()[1])
    ax.plot(lower, lower, "o", c="white", ms=1)
    ax.plot(upper, upper, "o", c="white", ms=1)


def save_scatter(ax, file, size):
    low_x = ax.get_xlim()[0]
    up_x = ax.get_xlim()[1]
    low_y = ax.get_ylim()[0]
    up_y = ax.get_ylim()[1]
    lower = max(ax.get_xlim()[0], ax.get_ylim()[0])
    upper = min(ax.get_xlim()[1], ax.get_ylim()[1])
    ax.plot(lower, lower, "o", c="white", ms=1)
    ax.plot(upper, upper, "o", c="white", ms=1)
    ax.set_axis_off()
    plt.savefig(file + ".png")

    def bbox(im):
        a = np.array(im)[:, :, :3]  # keep RGB only
        m = np.any(a != [255, 255, 255], axis=2)
        coords = np.argwhere(m)
        y0, x0, y1, x1 = *np.min(coords, axis=0), *np.max(coords, axis=0)
        return (x0, y0, x1 + 1, y1 + 1)

    im = Image.open(file + ".png")
    im2 = im.crop(bbox(im))
    im2.save(file + ".png")

    for el in plt.gca().lines + plt.gca().collections:
        el.remove()

    ax.set_xlim(low_x, up_x)
    ax.set_ylim(low_y, up_y)
    ax.plot([lower, upper], [lower, upper], ls="--", c=".3")

    ax.set_axis_on()
    tikzplotlib.save(file)

    with open(file, "r") as f:
        content = f.read()

    idx = content.index("\\begin{axis}")
    content = (
        content[:idx]
        + "\\node[inner sep=0pt,anchor=south west] at (0,0) {\includegraphics[width="
        + str(size)
        + "cm]{"
        + file
        + ".png}};\n"
        + content[idx:]
    )

    idx = content.index("\\begin{axis}[") + len("\\begin{axis}[")
    content = (
        content[:idx]
        + "\nwidth="
        + str(size)
        + "cm, height="
        + str(size)
        + "cm, scale only axis, at={(0,0)},"
        + content[idx:]
    )

    with open(file, "w") as f:
        f.write(content)
