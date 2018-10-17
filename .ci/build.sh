#!/usr/bin/env bash

mkdir -p build || return 1
cd build/ || return 1
cmake -D DEVELOPER=ON -D USE_COCOA=ON -D USE_GINAC=ON -D SMTRAT_Strategy=AllModulesStrategy ../ || return 1

function keep_waiting() {
  while true; do
    echo -e "."
    sleep 60
  done
}

if [[ ${TASK} == "dependencies" ]]; then
	
	keep_waiting &
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	kill $!
	
elif [[ ${TASK} == "doxygen" ]]; then
	
	cmake -D DOCUMENTATION_CREATE_PDF=ON ../
	make doc || return 1
	make manual || return 1
	
	git config --global user.email "gereon.kremer@cs.rwth-aachen.de"
	git config --global user.name "Travis doxygen daemon"
	
	git clone https://${GH_TOKEN}@github.com/smtrat/smtrat.github.io.git
	cd smtrat.github.io/ || return 1
	git branch -m master old_master
	git checkout --orphan master
	
	# Update cloned copy
	cp -r ../doc/html/* ./ || return 1
	cp ../doc/*.pdf .  || return 1
	cp ../manual/*.pdf .  || return 1
	
	# Check if something has changed
	git diff --summary --exit-code && return 0
	git add . || return 1
	
	# Commit and push
	git commit -q -m "Updated documentation for SMT-RAT" || return 1
	git push -f origin master || return 1

else
	keep_waiting &
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	kill $!
	/usr/bin/time make -j1 || return 1
fi

cd ../
