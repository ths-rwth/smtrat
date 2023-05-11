import pandas as pd

def get_solvers(df):
    return df.columns.get_level_values(0).unique()

def compare_results(answer1,time1,answer2,time2):
    if answer1 in ['sat','unsat'] and not answer2 in ['sat','unsat']:
        return True
    elif not answer1 in ['sat','unsat'] and answer2 in ['sat','unsat']:
        return False
    elif answer1 != 'unknown' and answer2 == 'unknown':
        return True
    elif answer1 == 'unknown' and answer2 != 'unknown':
        return False
    elif answer1 != 'memout' and answer2 == 'memout':
        return True
    elif answer1 == 'memout' and answer2 != 'memout':
        return False
    else:
        assert (answer1 in ['sat','unsat']) == (answer2 in ['sat','unsat'])
        assert ((answer1 == 'memout') == (answer2 == 'memout'))
        return int(time1)<int(time2)
    

def virtual_best(df, solvers, name, statistics=[]):
    data = []
    for _, row in df.iterrows():
        s = solvers[0]
        for solver in solvers:
            if compare_results(row[(solver,'answer')],row[(solver,'runtime')],row[(s,'answer')],row[(s,'runtime')]):
                s = solver
        assert row[(s,'answer')] in ['sat','unsat'] or not True in [row[(solver,'answer')] in ['sat','unsat'] for solver in solvers] 
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