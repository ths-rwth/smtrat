#!/usr/bin/env bash

git fetch --unshallow

if [[ ${TRAVIS_OS_NAME} == "linux" ]]; then

	mkdir -p ~/usr/bin/
	PREFIX=`cd ~/usr; pwd`

	if [ ! -f $PREFIX/bin/cmake ]; then
		wget -nv https://cmake.org/files/v3.10/cmake-3.10.2-Linux-x86_64.sh
		chmod +x cmake-3.10.2-Linux-x86_64.sh
		./cmake-3.10.2-Linux-x86_64.sh --prefix=$PREFIX --exclude-subdir --skip-license
	fi

	export PATH="$PREFIX/bin:$PATH"

elif [[ ${TRAVIS_OS_NAME} == "osx" ]]; then

	brew update --quiet
	brew upgrade cmake
	brew install llvm

fi

export CC=$CC
export CXX=$CXX
