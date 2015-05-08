#!/usr/bin/env bash

mkdir build || return 1
cd build/ || return 1
cmake -D DEVELOPER=ON ../ || return 1

if [[ ${TASK} == "doxygen" ]]; then
	make doc
	
	git config --global user.email "gereon.kremer@cs.rwth-aachen.de"
	git config --global user.name "Travis doxygen daemon"
	
	git clone https://219fc41efb80a7a8f102f5ca9147baf58514d734@github.com/smtrat/smtrat.github.io.git
	cd smtrat.github.io/
	
	cp ../doc/html/* ./
	git add .
	git commit -m "Updated documentation for SMT-RAT"
	git push origin master

else
	make -j4 || return 1
fi

cd ../
