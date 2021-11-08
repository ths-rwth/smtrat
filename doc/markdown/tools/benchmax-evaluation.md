# Benchmax python utility {#benchmax-evaluation}

This tool allows loading XML files from Benchmax into a pandas dataframe, inspecting the results and visualizing them.

This is useful for working with the results in a Jupyter notebook.

Dependencies:

* [pandas](https://pandas.pydata.org/)
* matplotlib
* pillow
* numpy
* [tikzplotlib](https://github.com/nschloe/tikzplotlib)

```bash
pip3 install pandas matplotlib tikzplotlib numpy pillow
```

## Loading XMLs into a pandas dataframe

First, install this directory as python library; e.g. on Ubuntu
```bash
cd ~/.local/lib/python3.8/site-packages/ # path to your python site-packages directory
ln -s ~/src/smtrat/utilities/benchmax/ # path to the benchmax utility
```

In your Jupyter notebook:

```python
import benchmax.evaluation as ev

df = ev.xml_to_pandas("path_to/stats_file.xml", {"smtrat-static": "solver_name"}, ["statistics_name_1","statistics_name_2"]) # second and third parameter is optional
```

or, to load multiplle XMLs into one:

```python
import benchmax.evaluation as ev

df = ev.xmls_to_pandas({"path_to/stats_file_1.xml": {"smtrat-static": "solver_name_1"}, "path_to/stats_file_2.xml": {"smtrat-static": "solver_name_2"}}, ["statistics_name_1","statistics_name_2"]) # second parameter is optional
```

This will create a dataframe with columns `(solver_name_1, "answer")`, `(solver_name_1, "runtime")`, `(solver_name_1, "statistics_name_1")` etc (as multi-index).

## Computing a virtual best solver

A virtual best is a solver that behaves optimal on each input w.r.t. a set of solvers. It is computed by selecting for each benchmark instance the solver with shortest running time. 

To compute the virtual best solver named `VB` w.r.t. `solver1`,`solver2` and `solver3` and considering statistics `statistics_name_1`.

```python
df = df.join(ev.virtual_best(df, ["solver1","solver2","solver3"], "VB", ['statistics_name_1']))
```

## Plotting

We provide the `performance_profile` and `scatter_plot` functions to easily generate a performance profiles and scatter plots.

## Show a summary of an XML file

There are several methods for quickly inspecting the results of a run provided. For instance, the following script can be used to view a summary of a singel XML file and to show instances with wrong results or segmentation faults:

```python
#!/usr/bin/env python3
import benchmax.evaluation as ev
import sys

df = ev.xml_to_pandas(sys.argv[1])
ev.inspect(df)
```

SMT-RAT provides a small utility script for showing a summary of one or more XML files:

```bash
~/Code/smtrat/utilities/benchmax/view.py result_1.xml result_2.xml
```

## Exporting data to Latex

### Pandas dataframe to latex table
```python
df.to_latex(buf='file.tex')
```

### matplotlib to tikz plot

see [tikzplotlib](https://github.com/nschloe/tikzplotlib)