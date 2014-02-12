/* 
 * File:   platform.h
 * Author: Florian Corzilius
 *
 * Created on February 12, 2014, 12:13 PM
 */

#pragma once

//////////////////////
// Compiler identification
// taken from http://sourceforge.net/p/predef/wiki/Compilers/

#define STRINGIFY(s) #s

#ifdef __clang__
    #define __CLANG

    #define CLANG_WARNING_DISABLE(warning)\
        _Pragma("clang diagnostic push")\
        _Pragma( STRINGIFY(clang diagnostic ignored warning) )
    #define CLANG_WARNING_RESET\
        _Pragma("clang diagnostic pop")
#elif __GNUC__
    #define __GCC
    
    #define CLANG_WARNING_DISABLE(warning)
    #define CLANG_WARNING_RESET
#else
    #warning "You are using an unsupported compiler."
    #define __UNSUPPORTED
#endif