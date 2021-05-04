#!/usr/bin/env bash

mkdir -p build || return 1
cd build/ || return 1
cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=AllModulesStrategy ../ || return 1


if [[ ${TASK} == "dependencies" ]]; then
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	/usr/bin/time make ${MAKE_PARALLEL} carl-required-version || return 1
	/usr/bin/time make ${MAKE_PARALLEL} mimalloc-EP || return 1
	
elif [[ ${TASK} == "documentation" ]]; then
	
	# To allow convert for doc/pictures/
	if ! command -v sudo &> /dev/null
	then
		rm -f /etc/ImageMagick-6/policy.xml
	else
		sudo rm -f /etc/ImageMagick-6/policy.xml
	fi

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
	/usr/bin/time make ${MAKE_PARALLEL} || return 1

elif [[ ${TASK} == "getCarl" ]]; then 
	#check if Carl branch with the same name exists and download the artifacts with the same job name
	CARL_ID=56538
	CARL_URL_OWN=https://git.rwth-aachen.de/api/v4/projects/${CARL_ID}/jobs/artifacts/${BRANCH_NAME}/download?job=${JOB_NAME}
	#URL for Development Branch
	CARL_URL_DEVELOP=https://git.rwth-aachen.de/api/v4/projects/${CARL_ID}/jobs/artifacts/${BRANCH_NAME}/download?job=${JOB_NAME}
	if curl -v -L --fail --output artifacts.zip --header "PRIVATE-TOKEN: ${TOKEN}" "${CARL_URL_OWN}" ; then 
		mkdir -p /builds/ths/smt/carl/
    	unzip -q artifacts.zip -d /builds/ths/smt/carl/
		#todo check for carl in build cache and remove it
	elif curl -v -L --fail --output artifacts.zip --header "PRIVATE-TOKEN: ${TOKEN}" "${CARL_URL_DEVELOP}" ; then
		mkdir -p /builds/ths/smt/carl/
    	unzip -q artifacts.zip -d /builds/ths/smt/carl/
		#todo check for carl in build cache and remove it 
	else 
    echo "Artifact for Carl Branch: ${BRANCH_NAME} and Job: ${JOB_NAME} and for Development Branch does not exist"
	fi
	cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=AllModulesStrategy -D carl_DIR=/builds/ths/smt/carl/build ../ || return 1
else
	#no task specified... just build with one core
	/usr/bin/time make -j1 || return 1
fi

cd ../
