# Utility for working with benchmark results in Python

This tool allows loading XML files from Benchmax into a SQLite Database and from there into a pandas dataframe.

This is useful for working with the results in a Jupyter notebook.

Required:

* [pandas](https://pandas.pydata.org/)
* sqlite3

Recommended:

* matplotlib
* [tikzplotlib](https://github.com/nschloe/tikzplotlib)

## Loading XMLs into SQLite

```python
import os
import sys
import sqlite3
module_path = os.path.abspath(os.path.join('..')) # replace ".." by relative path to the parent of this folder 
if module_path not in sys.path:
    sys.path.append(module_path)
import evaluation

evaluation.reset()
evaluation.load_file("path_to/stats_file.xml", {"smtrat-static": "other_folder_name"}) # second parameter is optinal
```

Doing so, a `db.db` file is created.

## Loading entries from the SQLite database into a pandas dataframe

```python
data = lib.get_table(solvers, 
    [
        ('solver_name', 'statistics_name', 'column_name_in_dataframe'), ...
    ])
).fillna(0)
```

## Snippets

### Latex export

* Pandas dataframe to latex table
    ```python
    df.to_latex(buf='file.tex')
    ```

* matplotlib to tikz plot: see [tikzplotlib](https://github.com/nschloe/tikzplotlib)