#!/usr/bin/env bash

mkdir -p build || return 1
cd build/ || return 1


if [[ ${TASK} == "dependencies" ]]; then
	echo "Building dependencies"
    cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} ../ || return 1
	/usr/bin/time make ${MAKE_PARALLEL} resources || return 1
	/usr/bin/time make ${MAKE_PARALLEL} carl-required-version || return 1
	/usr/bin/time make ${MAKE_PARALLEL} mimalloc-EP || return 1
	
elif [[ ${TASK} == "documentation" ]]; then
	echo "Building Documentation"
    cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} ../ || return 1
	
	# To allow convert for doc/pictures/
	if ! command -v sudo &> /dev/null
	then
		rm -f /etc/ImageMagick-6/policy.xml
	else
		sudo rm -f /etc/ImageMagick-6/policy.xml
	fi

	make doc || return 1
	
	git config --global user.email "admin@ths.rwth-aachen.de"
	git config --global user.name "Documentation daemon"
	
	git clone https://${GH_TOKEN}@github.com/ths-rwth/ths-rwth.github.io.git
	cd ths-rwth.github.io/ || return 1
	git branch -m master old_master
	git checkout --orphan master
	
	# Update cloned copy
	cp -r ../doc/apidoc-html/* smtrat/ || return 1
	cp ../doc/doc_smtrat-*.pdf .  || return 1
	cp ../doc/doc_smtrat-*.pdf doc_smtrat-latest.pdf  || return 1
	cp ../doc/manual_smtrat-*.pdf . || return 1
	cp ../doc/manual_smtrat-*.pdf manual_smtrat-latest.pdf || return 1
	
	# Check if something has changed
	# git diff --summary --exit-code && return 0
	git add . || return 1
	
	# Commit and push
	git commit -q -m "Updated documentation for SMT-RAT" || return 1
	git push -f origin master || return 1

elif [[ ${TASK} == "tidy" ]]; then
	echo "Tidying"
    cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} ../ || return 1
	/usr/bin/time make tidy || return 1

elif [[ ${TASK} == "parallel" ]]; then
	echo "Build parallel with parameter ${MAKE_PARALLEL}"
    cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} ../ || return 1
	/usr/bin/time make ${MAKE_PARALLEL} || return 1

elif [[ ${TASK} == "getCarl" ]]; then 
	#check if Carl branch with the same name exists and download the artifacts with the same job name
    echo "Trying to download Carl artifacts"
	echo "If a Carl-branch with the name name exists, it will be used. Otherwise the development branch is used"
	CARL_ID=56538
	CARL_URL_OWN=https://git.rwth-aachen.de/api/v4/projects/${CARL_ID}/jobs/artifacts/${BRANCH_NAME}/download?job=${JOB_NAME}
	#URL for Development Branch
	CARL_URL_DEVELOP=https://git.rwth-aachen.de/api/v4/projects/${CARL_ID}/jobs/artifacts/development/download?job=${JOB_NAME}
	if curl -L --fail --output artifacts.zip --header "PRIVATE-TOKEN: ${TOKEN}" "${CARL_URL_OWN}" ; then 
		echo "Found Carl-branch with name: " ${BRANCH_NAME} " and the download was successfull"
		mkdir -p /builds/ths/smt/carl/
    	unzip -o -q artifacts.zip -d /builds/ths/smt/carl/
	elif curl -L --fail --output artifacts.zip --header "PRIVATE-TOKEN: ${TOKEN}" "${CARL_URL_DEVELOP}" ; then
		echo "Used development branch and the download was successfull"
		mkdir -p /builds/ths/smt/carl/
    	unzip -o -q artifacts.zip -d /builds/ths/smt/carl/
	else 
    echo "Artifact for Carl Branch: ${BRANCH_NAME} and Job: ${JOB_NAME} and for Development Branch does not exist"
	fi
	cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} -D carl_DIR=/builds/ths/smt/carl/build ../ || return 1

else
	#no task specified... just build with one core
	echo "No task specified... building with one core"
	cmake -D DEVELOPER=ON -D USE_COCOA=ON -D SMTRAT_Strategy=${STRATEGY} ../ || return 1

	/usr/bin/time make -j1 || return 1
fi

cd ../
