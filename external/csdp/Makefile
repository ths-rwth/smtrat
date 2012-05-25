#
# This Makefile can be used to automatically build the entire package.  
#
# If you make changes in the "Makefile" under any subdirectory, you can
# rebuild the system with "make clean" followed by "make all".
#
#
# Generic. On most systems, this should handle everything.
#
all:
	cd lib; make libsdp.a
	cd solver; make csdp
	cd theta; make all
	cd example; make all

#
# Perform a unitTest
#

unitTest:
	cd test; make all

#
# Install the executables in /usr/bin.
#

install:
	cp -f solver/csdp /usr/bin
	cp -f theta/theta /usr/bin
	cp -f theta/graphtoprob /usr/bin
	cp -f theta/complement /usr/bin
	cp -f theta/rand_graph /usr/bin

	cp -f lib/libsdp.a /usr/lib
	cp -f include/* /usr/include/csdp





#
# Clean out all of the directories.
# 

clean:
	cd lib; make clean
	cd solver; make clean
	cd theta; make clean
	cd test; make clean
	cd example; make clean








