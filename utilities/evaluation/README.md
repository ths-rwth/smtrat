# Utility for working with benchmark results in Python

This tool allows loading XML files from Benchmax into a SQLite Database and from there into a pandas dataframe.

This is useful for working with the results in a Jupyter notebook.

Required:

* [pandas](https://pandas.pydata.org/)
* (sqlite3)

```bash
pip3 install pandas 
```

Recommended:

* matplotlib
* [tikzplotlib](https://github.com/nschloe/tikzplotlib)

```bash
pip3 install matplotlib tikzplotlib
```

## Loading XMLs into a pandas dataframe

First, install this directory as python library; e.g. on Ubuntu
```bash
cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
ln -s ~/src/smtrat/utilities/evaluation # path to this directory
```

In your Jupyter notebook:

```python
import evaluation

df = evaluation.xml_to_pandas("path_to/stats_file.xml", {"smtrat-static": "solver_name"}, ["statistics_name_1","statistics_name_2"]) # second and third parameter is optional
```

## Snippets

### Latex export

* Pandas dataframe to latex table
    ```python
    df.to_latex(buf='file.tex')
    ```

* matplotlib to tikz plot: see [tikzplotlib](https://github.com/nschloe/tikzplotlib)