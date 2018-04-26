#!/usr/bin/env bash

git fetch --unshallow

if [[ ${TRAVIS_OS_NAME} == "linux" ]]; then

	mkdir -p ~/usr/bin/
	PREFIX=`cd ~/usr; pwd`
	
	if [[ ${TASK} == "doxygen" ]]; then
		if [ ! -f $PREFIX/bin/doxygen ]; then
			wget -nv http://ftp.stack.nl/pub/users/dimitri/doxygen-1.8.14.linux.bin.tar.gz
			tar -xzf doxygen-1.8.14.linux.bin.tar.gz -C $PREFIX/bin/
			cp $PREFIX/bin/doxygen-*/bin/* $PREFIX/bin/
		fi
	fi

	export PATH="$PREFIX/bin:$PATH"

fi

export CC=$CC
export CXX=$CXX
