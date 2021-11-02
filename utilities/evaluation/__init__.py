from .load import xml_to_pandas, xmls_to_pandas
from .data import filter_solved, cumulate_by_column, virtual_best
from .plots import performance_profile, scatter_plot
from .inspect import *

# TODO remove:
from .legacy.collect import load_file
from .legacy.pdadaptor import get_table,get_table_by_example
from .legacy.database import reset,get_solvers,conn