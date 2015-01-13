#!/usr/bin/env bash

source setup_common.sh

function install {
	sudo apt-get -qq install --force-yes $*
}

sudo apt-get -qq update

install cmake libboost1.55-all-dev libcln-dev libeigen3-dev libgtest-dev libstdc++-4.9-dev

if [[ ${USE} == "g++-4.8" ]]; then
	install gcc-4.8 g++-4.8
	defCXX gcc-4.8 g++-4.8
elif [[ ${USE} == "g++-4.9" ]]; then
	install gcc-4.9 g++-4.9
	defCXX gcc-4.9 g++-4.9
elif [[ ${USE} == "clang++-3.3" ]]; then
	install clang-3.3
	defCXX clang clang++
elif [[ ${USE} == "clang++-3.4" ]]; then
	install clang-3.4
	defCXX clang-3.4 clang++-3.4
elif [[ ${USE} == "clang++-3.5" ]]; then
	install clang-3.5
	defCXX clang-3.5 clang++-3.5
fi
