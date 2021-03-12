#!/usr/bin/env bash

mkdir -p build || return 1
cd build/ || return 1
cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=AllModulesStrategy ../ || return 1

function keep_waiting() {
  while true; do
    echo -e "."
    sleep 60
  done
}
function start_keep_waiting() {
  keep_waiting &
  disown
  keep_waiting_id=$!
}
function stop_keep_waiting() {
  kill $keep_waiting_id
}

if [[ ${TASK} == "dependencies" ]]; then
	
	start_keep_waiting
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	stop_keep_waiting
	
elif [[ ${TASK} == "documentation" ]]; then
	
	# To allow convert for doc/pictures/
	sudo rm -f /etc/ImageMagick-6/policy.xml

	make doxygen-build || return 1
	make doc || return 1
	
	git config --global user.email "gereon.kremer@cs.rwth-aachen.de"
	git config --global user.name "Travis doxygen daemon"
	
	git clone https://${GH_TOKEN}@github.com/smtrat/smtrat.github.io.git
	cd smtrat.github.io/ || return 1
	git branch -m master old_master
	git checkout --orphan master
	
	# Update cloned copy
	cp -r ../doc/apidoc-html/* ./ || return 1
	cp ../doc/doc_smtrat-*.pdf .  || return 1
	cp ../doc/doc_smtrat-*.pdf doc_smtrat-latest.pdf  || return 1
	cp ../doc/manual_smtrat-*.pdf . || return 1
	cp ../doc/manual_smtrat-*.pdf manual_smtrat-latest.pdf || return 1
	
	# Check if something has changed
	git diff --summary --exit-code && return 0
	git add . || return 1
	
	# Commit and push
	git commit -q -m "Updated documentation for SMT-RAT" || return 1
	git push -f origin master || return 1

elif [[ ${TASK} == "tidy" ]]; then

	/usr/bin/time make tidy || return 1

elif [[ ${TASK} == "parallel" ]]; then
	start_keep_waiting
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	stop_keep_waiting
	/usr/bin/time make ${MAKE_PARALLEL} || return 1
else
	start_keep_waiting
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	stop_keep_waiting
	/usr/bin/time make -j1 || return 1
fi

cd ../
