#!/usr/bin/env bash

source setup_common.sh

cmake --version

if [[ ${USE} == "g++-4.8" ]]; then
	defCXX gcc-4.8 g++-4.8
elif [[ ${USE} == "g++-4.9" ]]; then
	defCXX gcc-4.9 g++-4.9
elif [[ ${USE} == "g++-5" ]]; then
	defCXX gcc-5 g++-5
elif [[ ${USE} == "g++-6" ]]; then
	defCXX gcc-6 g++-6
elif [[ ${USE} == "clang++-3.5" ]]; then
	defCXX clang-3.5 clang++-3.5
elif [[ ${USE} == "clang++-3.6" ]]; then
	defCXX clang-3.6 clang++-3.6
elif [[ ${USE} == "clang++-3.7" ]]; then
	defCXX clang-3.7 clang++-3.7
elif [[ ${USE} == "clang++-3.8" ]]; then
	defCXX clang-3.8 clang++-3.8
elif [[ ${USE} == "clang++-3.9" ]]; then
	defCXX clang-3.9 clang++-3.9
elif [[ ${USE} == "clang++-4.0" ]]; then
	defCXX clang-4.0 clang++-4.0
elif [[ ${USE} == "clang++-5.0" ]]; then
	defCXX clang-5.0 clang++-5.0
fi
