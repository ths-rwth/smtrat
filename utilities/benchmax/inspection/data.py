from itertools import chain, combinations
import pandas as pd


def get_solvers(df):
    return df.columns.get_level_values(0).unique()


def get_fields(df, solver):
    return [c[1] for c in df.columns if solver == c[0]]


# is only used by virtual_best
def compare_results(answer1, time1, answer2, time2):
    if answer1 in ["sat", "unsat"] and not answer2 in ["sat", "unsat"]:
        return True
    elif not answer1 in ["sat", "unsat"] and answer2 in ["sat", "unsat"]:
        return False
    elif answer1 == "success" and answer2 != "success":
        return True
    elif answer1 != "success" and answer2 == "success":
        return False
    elif answer1 != "unknown" and answer2 == "unknown":
        return True
    elif answer1 == "unknown" and answer2 != "unknown":
        return False
    elif answer1 != "memout" and answer2 == "memout":
        return True
    elif answer1 == "memout" and answer2 != "memout":
        return False
    else:
        assert (answer1 in ["sat", "unsat"]) == (answer2 in ["sat", "unsat"])
        assert (answer1 == "success") == (answer2 == "success")
        assert (answer1 == "memout") == (answer2 == "memout")
        return int(time1) < int(time2)


def virtual_best(df, solvers, name, statistics=[]):
    """
    computes a virtual best solver with the given name from the given solvers:
    for each row of df, the fastest solver defines the basic data (and the specified statistics) of the virtual best.
    Returns a df containing only the data of the virtual best.
    """
    data = []
    for _, row in df.iterrows():
        s = solvers[0]
        for solver in solvers:
            if compare_results(
                row[(solver, "answer")],
                row[(solver, "runtime")],
                row[(s, "answer")],
                row[(s, "runtime")],
            ):
                s = solver
        assert row[(s, "answer")] in ["sat", "unsat", "success"] or not True in [
            row[(solver, "answer")] in ["sat", "unsat", "success"] for solver in solvers
        ]
        new_row = []
        new_row.append(row[(s, "answer")])
        new_row.append(row[(s, "runtime")])
        for stat in statistics:
            if stat in row[s]:
                new_row.append(row[(s, stat)])
            else:
                new_row.append(None)

        data.append(tuple(new_row))
    columns = ["answer", "runtime"] + statistics
    return pd.DataFrame(
        data, df.index, columns=pd.MultiIndex.from_product([[name], columns])
    )


def filter_solved(df, solver):
    return df.loc[df[(solver, "answer")].isin(["sat", "unsat", "success"])].copy()


def filter(df, solved_by=[], not_solved_by=[]):
    df = df.copy()
    for s in solved_by:
        df = df[df[(s, "answer")].isin(["sat", "unsat", "success"])]
    for s in not_solved_by:
        df = df[~df[(s, "answer")].isin(["sat", "unsat", "success"])]
    return df


# basically only used by performance_profile
def cumulate_by_column(df, column):
    df.loc[:, "num"] = 1
    df = df.groupby([column]).count()
    df.loc[:, "num"] = df["num"].cumsum()
    df = df[["num"]]
    df = df.reset_index().set_index("num")
    return df


def solved_by_class(df, solvers):
    """
    if the benchmark instances are structured into multiple directories,
    then this can be used to get (as the returned df) the number of solved instances
    for each of the given solvers and each of these directories.
    """
    df = df.loc[:, [(s, "answer") for s in solvers]]
    df = df.droplevel(1, 1)
    df = df.replace(
        {
            "sat": 1,
            "unsat": 1,
            "success": 1,
            "unknown": 0,
            "wrong": 0,
            "error": 0,
            "timeout": 0,
            "memout": 0,
            "no answer": 0,
            "segmentation fault": 0,
            "segfault": 0,
            "abort": 0,
            "invalid": 0,
        }
    )
    df["total"] = 1
    df = df.groupby(df.index.to_series().str.split("/").str[0]).sum()
    return df


def unique_solved_instances(df, solvers):
    result_labels = []
    results = []

    for group in chain.from_iterable(
        combinations(solvers, r) for r in range(len(solvers) + 1)
    ):
        df2 = df
        for t in group:
            df2 = df2[df2[(t, "answer")].isin(["sat", "unsat", "success"])]
        for t in (t for t in solvers if t not in group):
            df2 = df2[~df2[(t, "answer")].isin(["sat", "unsat", "success"])]
        result_labels.append(group)
        results.append(
            (
                df2.shape[0],
                df2.shape[0] / df.shape[0],
            )
        )
    return pd.DataFrame(
        results,
        index=result_labels,
        columns=["num. unique instances", "rel. unique instances"],
    )

def compare_attribute(df,solver1,solver2,col):
    solved_both = filter(df, solved_by=[solver1,solver2]).loc[:,col].fillna(0)
    solved_solver1 = filter(df, solved_by=[solver1], not_solved_by=[solver2]).loc[:,col].fillna(0)
    solved_solver2 = filter(df, not_solved_by=[solver1], solved_by=[solver2]).loc[:,col].fillna(0)        
    solved_none = filter(df, not_solved_by=[solver1,solver2]).loc[:,col].fillna(0)   

    results = [
        (solved_both.mean()   ,solved_both.median()   ,solved_both.min()   ,solved_both.max(),),
        (solved_solver1.mean(),solved_solver1.median(),solved_solver1.min(),solved_solver1.max(),),
        (solved_solver2.mean(),solved_solver2.median(),solved_solver2.min(),solved_solver2.max(),),
        (solved_none.mean(),solved_none.median(),solved_none.min(),solved_none.max(),)
    ]
    return pd.DataFrame(results,columns=['mean','median','min','max'], index=['both','only '+solver1,'only '+solver2,'none'])

def compare_attributes(df,solver1,solver2,cols):
    solved_both = filter(df, solved_by=[solver1,solver2])
    solved_solver1 = filter(df, solved_by=[solver1], not_solved_by=[solver2])
    solved_solver2 = filter(df, not_solved_by=[solver1], solved_by=[solver2])
    solved_none = filter(df, not_solved_by=[solver1,solver2])
    results = [
        (len(solved_both),),(len(solved_solver1),),(len(solved_solver2),),(len(solved_none),)
    ]
    numinst = pd.DataFrame(results,columns=['solved'], index=['both','only '+solver1,'only '+solver2,'none'])

    return pd.concat([numinst] + [compare_attribute(df,solver1,solver2,col) for col in cols], axis=1,keys=['instances']+cols)