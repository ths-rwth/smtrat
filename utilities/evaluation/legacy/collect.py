import glob
import logging

from . import database
from . import loader

def load_file(pattern, mapping):
    for file in glob.glob(pattern):
	    loader.load(file, mapping)
	    loader.load_info(file, mapping)
    database.commit()