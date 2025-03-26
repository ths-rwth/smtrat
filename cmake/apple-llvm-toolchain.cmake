# Detect clang version, switch to homebrew llvm automatically
if(APPLE)
	set(USE_LLVM_FROM_BREW NO)
	set(LIB_FILESYSTEM "c++fs")
	#if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS 10.0)
	#	message(STATUS "clang ${CMAKE_CXX_COMPILER_VERSION} does not support C++17.")
	#	set(USE_LLVM_FROM_BREW YES)
	#else()
	#	exec_program("sw_vers -productVersion" OUTPUT_VARIABLE MACOS_VERSION)
	#	if (MACOS_VERSION VERSION_LESS 10.14)
	#		message(STATUS "Found Mac OS X in version ${MACOS_VERSION} but version >= 10.14 needed for the proper libc++.")
	#		set(USE_LLVM_FROM_BREW YES)
	#	endif()
	#endif()

	#if(USE_LLVM_FROM_BREW)
		if(EXISTS "/usr/local/Cellar/llvm/8.0.0/bin/clang++")
			set(CMAKE_C_COMPILER /usr/local/Cellar/llvm/8.0.0/bin/clang CACHE PATH "" FORCE)
			set(CMAKE_CXX_COMPILER /usr/local/Cellar/llvm/8.0.0/bin/clang++ CACHE PATH "" FORCE)
			set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -I/usr/local/Cellar/llvm/8.0.0/include -I/usr/local/Cellar/llvm/8.0.0/include/c++/v1/")
			set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -L/usr/local/Cellar/llvm/8.0.0/lib -Wl,-rpath,/usr/local/Cellar/llvm/8.0.0/lib")
			set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -L//usr/local/Cellar/llvm/8.0.0/lib -Wl,-rpath,/usr/local/Cellar/llvm/8.0.0/lib")
			exec_program("${CMAKE_CXX_COMPILER} --version" OUTPUT_VARIABLE tmp_version)
			string(REGEX REPLACE ".*version ([0-9.]+).*" "\\1" CMAKE_CXX_COMPILER_VERSION "${tmp_version}")
			if(CMAKE_CXX_COMPILER_VERSION VERSION_LESS 7)
				set(LIB_FILESYSTEM "c++experimental")
			endif()
			message(STATUS "Auto-detected brew-installed llvm version ${CMAKE_CXX_COMPILER_VERSION}")
		else()
			message(FATAL_ERROR "Did not find a proper compiler. Please run \"brew install llvm\" or upgrade to XCode >= 10.1.")
		endif()
	#endif()
endif()
