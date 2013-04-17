/* ---------------------------------------------------------------------
   $Id: RedMsg.c 102 2009-02-28 19:13:45Z thomas-sturm $
   ---------------------------------------------------------------------
   Copyright (c) 2008-2009 Thomas Sturm
   ---------------------------------------------------------------------
   Redistribution and use in source and binary forms, with or without
   modification, are permitted provided that the following conditions
   are met:
  
      * Redistributions of source code must retain the relevant
        copyright notice, this list of conditions and the following
        disclaimer.
      * Redistributions in binary form must reproduce the above
        copyright notice, this list of conditions and the following
        disclaimer in the documentation and/or other materials provided
        with the distribution.
  
   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
   OWNERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <errno.h>

#include "RedMsg.h"

FILE *RedMsg_openLogfile(const char *filename,FILE *handle) {
  if (handle)
    return handle;
    
  handle = fopen(filename,"w");

  if (!handle) {
    char emsg[1024];
    
    sprintf(emsg,"libreduce cannot open %s",filename);
    perror(emsg);
    exit(errno);
  }

  return handle;
}

int RedMsg_cfprintf(FILE *file,const char *msg,...) {
  int ecode=0;
  if (file) {
    va_list ap;
  
    va_start(ap,msg);
    ecode = vfprintf(file,msg,ap);
    va_end(ap);
    fflush(file);
  }

  return ecode;
}
