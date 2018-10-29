#!/usr/bin/env bash

git fetch --unshallow

if [[ ${TRAVIS_OS_NAME} == "osx" ]]; then

	brew update --quiet
	brew upgrade cmake
	brew install llvm

fi

export CC=$CC
export CXX=$CXX
