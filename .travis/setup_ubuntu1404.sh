#!/usr/bin/env bash

source setup_common.sh

function install {
	sudo apt-get -qq install --force-yes $*
}

sudo add-apt-repository -y ppa:ubuntu-toolchain-r/test
sudo apt-get -qq update

install cmake doxygen libboost1.55-all-dev libcln-dev libeigen3-dev libgtest-dev

if [[ ${USE} == "g++-4.8" ]]; then
	install gcc-4.8 g++-4.8
	defCXX gcc-4.8 g++-4.8
elif [[ ${USE} == "g++-4.9" ]]; then
	install gcc-4.9 g++-4.9
	defCXX gcc-4.9 g++-4.9
elif [[ ${USE} == "g++-5.1" ]]; then
	install gcc-5 g++-5
	defCXX gcc-5 g++-5
elif [[ ${USE} == "clang++-3.4" ]]; then
	install clang-3.4
	defCXX clang clang++
elif [[ ${USE} == "clang++-3.5" ]]; then
	install clang-3.5
	defCXX clang-3.5 clang++-3.5
elif [[ ${USE} == "clang++-3.6" ]]; then
	sudo add-apt-repository -y "deb http://llvm.org/apt/precise/ llvm-toolchain-precise-3.6 main"
	sudo apt-get -qq update
	install clang-3.6
	defCXX clang-3.6 clang++-3.6
elif [[ ${USE} == "clang++-3.7" ]]; then
	sudo add-apt-repository -y "deb http://llvm.org/apt/precise/ llvm-toolchain-precise-3.7 main"
	sudo apt-get -qq update
	install clang-3.7
	defCXX clang-3.7 clang++-3.7
fi

sudo service postgresql stop
sudo service mysql stop
sudo service cron stop

ps aux
