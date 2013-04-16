/* ---------------------------------------------------------------------
   $Id: StrBuf.c 519 2010-01-01 19:40:13Z thomas-sturm $
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
#include <stdlib.h>
#include "StrBuf.h"

StrBuf StrBuf_addChar(StrBuf b,char c) {
  /* Add c to b */
  StrBuf new;

  new = (StrBuf)malloc(sizeof(struct oStrBuf));
  new->c = c;
  new->next = (StrBuf)0;
  new->prev = b;
  if (b)
    b->next = new;
  return new;
}

StrBuf StrBuf_pruneNl(StrBuf b) {
  StrBuf h;

  if (b == NULL)
    return NULL;

  while (b && b->c == 0x0a) {
    h = b;
    b = b->prev;
    free(h);
    if (b)
      b->next = 0;
  }
  
  if (b == NULL)
    return NULL;

  while (b->prev)
    b = b->prev;
  
  while (b->c == 0x0a) {
    b = b->next;
    free(b->prev);
    b->prev = 0;
  }

  while (b->next)
    b = b->next;
  
  return b;
}

char *StrBuf_string(StrBuf b) {
  /* Convert b into a string, and free b */
  char *bstring;
  int len,i;
  
  if (b == NULL)
    return NULL;
  
  len = 1;

  while (b->prev) {
    len++;
    b = b->prev;
  }

  bstring = (char *)malloc(len*sizeof(char)+1);

  for (i=0; i<len-1; i++) {
    bstring[i] = b->c;
    b = b->next;
    free(b->prev);
  }
  
  bstring[len-1] = b->c;
  bstring[len] = 0;
  free(b);

  return bstring;
}

/* unused */

StrBuf StrBuf_remTail(StrBuf b,StrBuf t) {
  /* It is assumed that b=wtw'. Returns w. */
  while (!StrBuf_tailIs(b,t))
    b = b->prev;
  
  while (t) {
    t = t->prev;
    b = b-> prev;
    free(b->next);
  }

  b->next = (StrBuf)0;
  
  return b;
}

int StrBuf_tailIs(StrBuf b,StrBuf t) {
  /* Return nonzero iff t is the tail of b. */
  while (t) {
    if (t->c != b->c)
      return 0;
    t = t->prev;
    b = b->prev;
  }
  return 1;
}

void StrBuf_fprint(FILE *file,StrBuf b) {
  StrBuf scan,old;

  if (!b)
    return;

  scan = b;
  while (scan->prev)
    scan = scan->prev;

  while (scan) {
    fprintf(file,"%c",scan->c);
    old = scan;
    scan = scan->next;
    free(old);
  }
  
  fflush(file);
}
