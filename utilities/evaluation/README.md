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

First, install this directory as python library; e.g. on Ubuntu
```bash
cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
ln -s ~/src/smtrat/utilities/evaluation # path to this directory
```

In your Jupyter notebook:

```python
import evaluation

evaluation.reset()
evaluation.load_file("path_to/stats_file.xml", {"smtrat-static": "solver_name"}) # second parameter is optinal
```

Doing so, a `db.db` file is created.

## Loading entries from the SQLite database into a pandas dataframe

```python
data = evaluation.get_table(solvers, 
    [
        ('solver_name', 'statistics_name'), ...
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