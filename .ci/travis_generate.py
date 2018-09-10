#!/usr/bin/env python3

import sys

if len(sys.argv) > 1:
	sys.path.insert(0, sys.argv[1])

from travis_helper import *

jobs = [
	job("0-clang", ["dependencies", "linux", "clang-3.8", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-3.8", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-3.9", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-3.9", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-4.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-4.0", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-5.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-5.0", "build.sh"]),
	job("0-clang", ["dependencies", "linux", "clang-6.0", "build.sh"]),
	job("0-clang", ["build", "linux", "clang-6.0", "build.sh"]),
	job("1-gcc", ["dependencies", "linux", "g++-7", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["build", "linux", "g++-7", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["dependencies", "linux", "g++-8", "j1", "build.sh", "mayfail"]),
	job("1-gcc", ["build", "linux", "g++-8", "j1", "build.sh", "mayfail"]),
	job("2-macos", ["build", "xcode7.3", "build.sh"]),
	job("2-macos", ["build", "xcode8.3", "build.sh"]),
	job("2-macos", ["build", "xcode9", "build.sh"]),
	job("2-macos", ["build", "xcode9.1", "build.sh"]),
	job("2-macos", ["build", "xcode9.2", "build.sh"]),
	job("2-macos", ["build", "xcode9.3", "build.sh"]),
	job("2-macos", ["build", "xcode9.4", "build.sh"]),
	job("2-macos", ["build", "xcode10", "build.sh"]),
	job("3-docs", ["build", "linux", "clang-6.0", "task.doxygen", "j1", "build.sh"]),
]


cached = [
	"$HOME/usr/",
	"$HOME/carl/",
	"build/resources",
]

render_template(jobs, cached)
