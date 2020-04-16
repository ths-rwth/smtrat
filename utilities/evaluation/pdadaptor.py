import pandas as pd
import sqlite3
from . import database


def chunks(lst, n):
    """Yield successive n-sized chunks from lst."""
    for i in range(0, len(lst), n):
        yield lst[i:i + n]

def get_table(solvers, statistics = []):
    df =  get_table_sub(solvers, []).set_index('file')

    for stats in chunks(statistics, 60):
        df2 = get_table_sub([], stats)
        df = df.merge(df2.set_index('file'))

    return df

def get_table_sub(solvers, statistics = []):
    query = ""
    query += "SELECT files.id AS file, files.filename AS name "
    query += " ".join(map(lambda solver: ", `"+solver+"`.answer AS `"+solver+"_answer`, `"+solver+"`.runtime AS `"+solver+"_runtime`", solvers))
    query += " ".join(map(lambda stat: ", CAST(`d_"+stat[0]+"_"+stat[1]+"`.value AS NUMERIC) AS `"+stat[0]+"_"+stat[2]+"`", filter(lambda stat: len(stat) < 4 or stat[3], statistics)))
    query += " ".join(map(lambda stat: ", `d_"+stat[0]+"_"+stat[1]+"`.value AS `"+stat[0]+"_"+stat[2]+"`", filter(lambda stat: len(stat) >= 4 and not stat[3], statistics)))
    query += " FROM files "
    query += " ".join(map(lambda solver: " LEFT JOIN data AS `"+solver+"` ON files.id = `"+solver+"`.file AND `"+solver+"`.solver = '"+solver+"'", solvers))
    query += " ".join(map(lambda stat: " LEFT JOIN  file_properties AS `d_"+stat[0]+"_"+stat[1]+"` ON `d_"+stat[0]+"_"+stat[1]+"`.solver = '"+stat[0]+"' AND `d_"+stat[0]+"_"+stat[1]+"`.name = '"+stat[1]+"' AND `d_"+stat[0]+"_"+stat[1]+"`.file = files.id", statistics))
    
    return pd.read_sql_query(query, database.conn)

def get_table_by_example(solvers, statistics = []):
    def subquery(solver):
        query = ""
        query += "SELECT data.solver AS solver, files.id AS file, files.filename AS name, data.answer AS answer, data.runtime AS runtime"
        query += " ".join(map(lambda stat: ", CAST(`d_"+stat[1]+"`.value AS NUMERIC) AS `"+stat[2]+"`", filter(lambda stat: stat[0] == solver and stat[3], statistics)))
        query += " ".join(map(lambda stat: ", `d_"+stat[1]+"`.value AS `"+stat[2]+"`", filter(lambda stat: stat[0] == solver and not stat[3], statistics)))
        query += " FROM files, data "
        query += " ".join(map(lambda stat: " LEFT JOIN file_properties AS `d_"+stat[1]+"` ON `d_"+stat[1]+"`.solver = data.solver AND `d_"+stat[1]+"`.name = '"+stat[1]+"' AND `d_"+stat[1]+"`.file = files.id", filter(lambda stat: stat[0] == solver, statistics)))
        query += " WHERE files.id = data.file AND data.solver = '"+solver+"'"
        return query

    dfs = []
    for solver in solvers:
        df = pd.read_sql_query(subquery(solver), database.conn)
        dfs.append(df)
            
    return pd.concat(dfs)