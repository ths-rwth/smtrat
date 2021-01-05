#!/bin/sh

solver=smtrat-static
mimalloc=resources/lib/mimalloc-1.6/libmimalloc.so

echo "Copying smtrat from build/"
cp ../../build/$solver bin/smtrat
strip bin/smtrat

echo "Copying mimallox from build/"
cp ../../build/$mimalloc bin/libmimalloc.so

echo "Creating archive"
tar -czf $solver.tgz bin/
