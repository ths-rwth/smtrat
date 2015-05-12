#!/usr/bin/env bash

if [[ ${TASK} == "doxygen" ]]; then
	export TASK="clang++-3.5"
	export USE="clang++-3.5"
	git clone https://github.com/nafur/carl.git
	cd carl/.travis/
	source setup_travis.sh || return 1
	cd ../
	source .travis/build.sh || return 1
	cd ../
	export TASK="doxygen"
	export USE="doxygen"
else
	git clone https://github.com/nafur/carl.git
	cd carl/.travis/
	source setup_travis.sh || return 1
	cd ../
	source .travis/build.sh || return 1
	cd ../
fi

if [[ ${TRAVIS_OS_NAME} == "linux" ]]; then

	source setup_ubuntu1204.sh

elif [[ ${TRAVIS_OS_NAME} == "osx" ]]; then

	source setup_osx.sh

fi
