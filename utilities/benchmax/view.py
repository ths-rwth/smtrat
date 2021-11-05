#!/usr/bin/env python3
import evaluation as ev
import sys

xmls = {}

for i in range(1,len(sys.argv)):
    xmls[sys.argv[i]] = {}
    
df = ev.xmls_to_pandas(xmls,['peak_memory_kbytes'])
ev.inspect(df)
