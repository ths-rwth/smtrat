#!/usr/bin/env bash

source setup_common.sh


function install {
	brew install $*
}

brew update --quiet
brew install cln cmake doxygen eigen llvm

if [[ ${USE} == "g++-4.8" ]]; then
	echo "g++-4.8 is not supported"
	#install gcc-4.8 g++-4.8
	#defCXX gcc-4.8 g++-4.8
elif [[ ${USE} == "g++-4.9" ]]; then
	install gcc
	defCXX gcc-4.9 g++-4.9
elif [[ ${USE} == "clang++-3.4" ]]; then
	echo "clang++-3.4 is not supported"
	#install clang-3.4
	#defCXX clang-3.4 clang++-3.4
elif [[ ${USE} == "clang++-3.5" ]]; then
	defCXX clang clang++
fi
