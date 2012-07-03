/*
 * File:   debug.h
 * Author: square
 *
 * Created on April 5, 2012, 2:48 PM
 */

#ifndef DEBUG_H
#define DEBUG_H

#include <iostream>

#define PRINTDEBUG
#define DEBUGLVL 5

#ifdef PRINTDEBUG
#define print_debug(mess,lvl) if(((lvl) < (DEBUGLVL))) (std::cout << "debug: " << (mess) << std::endl)
#else
#define print_debug(mess,lvl) ;
#endif

#endif   /* DEBUG_H */

