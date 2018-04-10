#!/usr/bin/env bash

function keep_waiting() {
  while true; do
    echo -e "."
    sleep 60
  done
}

git fetch --unshallow

pushd `pwd`
cd ~/
git clone https://github.com/smtrat/carl.git

cd carl/
echo "Checked out CArL version $(git describe --always)"
mkdir -p build || return 1
cd build/ || return 1
cmake -D DEVELOPER=ON ../ || return 1

keep_waiting &
make resources -j1 || return 1
make -j1 lib_carl || return 1
kill $!

popd

export CC=$CC
export CXX=$CXX
