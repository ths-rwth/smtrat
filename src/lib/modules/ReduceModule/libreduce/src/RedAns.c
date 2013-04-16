/* ---------------------------------------------------------------------
   $Id: RedAns.c 938 2010-11-24 22:11:39Z thomas-sturm $
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

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

#include <stdlib.h>
#include <string.h>

#include "reduce.h"
#include "RedMsg.h"
#include "StrBuf.h"
#include "RedAns.h"

#ifdef PSLFIX
#define SYSMAXBUFFER 200
#endif

#define READBUFSIZE 1024

#define PRETEXT 0x00
#define PROMPT 0x01
#define FINISHED 0x02
#define RESULT 0x03
#define STATCOUNTER 0x04
#define MODE 0x05
#define POSTTEXT 0x06

#define ISCOLOR(c) ((c) <= POSTTEXT)

#define COLORTAB {"PRETEXT","PROMPT","FINISHED","RESULT","STATCOUNTER","MODE","POSTTEXT"};

#define EOT 0x04
#define LF 0x0a

extern FILE *debugfile,*logfile;

void RedAns_loadInitFile(RedProc process) {
  RedMsg_cfprintf(debugfile,"-> RedAns_loadInitFile: entering\n");

  RedAns_delete(RedAns_new(process,"load_package libreduce$"));

  RedMsg_cfprintf(debugfile,"<- RedAns_loadInitFile: leaving\n");
}

RedAns RedAns_new(RedProc process,const char *command) {
  static int realinput=0;
  RedAns output;

  RedMsg_cfprintf(debugfile,"-> reduce_command: entering\n");

  if (realinput)
    RedMsg_cfprintf(logfile,
		    "pid = %d\ncommand = %s\n",process->processId,command);

  RedAns_sendReduce(process,command);

  output = RedAns_readUntilPrompt(process);

  if (realinput) {
    RedAns_cfprint(logfile,output);
    RedMsg_cfprintf(logfile,"\n");
  }

  RedMsg_cfprintf(debugfile,"<- reduce_command: leaving\n");

  realinput = 1;

  return output;
}

void RedAns_sendReduce(RedProc process,const char *command) {
  char ch;
  int ii;

  RedMsg_cfprintf(debugfile,
		  "-> RedAns_sendReduce: entering, command=%s\n",
		  command);

  if (command == (char *)NULL) {
    ch = EOT;
    write(process->meToReduce[1],&ch,1);
    ch = LF;
    write(process->meToReduce[1],&ch,1);
  } else {
    for (ii=0; command[ii] != 0; ii++) {
      ch = command[ii] & 0x7f;
      RedMsg_cfprintf(process->rlgFile,"%c",ch);
      write(process->meToReduce[1],&ch,1);
#ifdef PSLFIX
      if ((ii+1) % SYSMAXBUFFER == 0) {
	RedAns_delete(RedAns_readUntilPrompt(process));
	RedMsg_cfprintf(debugfile,
			"-- RedAns_sendReduce: skipped prompt (SYSMAXBUFFER=%d)\n",
			SYSMAXBUFFER);
      }
#endif
    }
    ch = LF;
    RedMsg_cfprintf(process->rlgFile,"%c",ch);
    write(process->meToReduce[1],&ch,1);
  }

  RedMsg_cfprintf(debugfile,"<- RedAns_sendReduce: leaving\n");
}

RedAns RedAns_readUntilPrompt(RedProc process) {
  int statcounter=-1,symbolic=-1;
  StrBuf statcbuf=(StrBuf)0;
  StrBuf pretext=(StrBuf)0;
  StrBuf result=(StrBuf)0;
  StrBuf posttext=(StrBuf)0;
  StrBuf nextprompt=(StrBuf)0;
  int time=-1,gctime=-1;
  RedAns ans;

  RedMsg_cfprintf(debugfile,"-> RedAns_readUntilPrompt: entering\n");

  RedAns_dfa(process,&statcbuf,&symbolic,&pretext,&result,
	     &posttext,&nextprompt);

  ans = (RedAns)malloc(sizeof(struct oRedAns));

  if (statcbuf) {
    char *statc = StrBuf_string(statcbuf);
    sscanf(statc,"%d",&statcounter);
    free(statc);
  }
  ans->statcounter = statcounter;

  ans->symbolic = symbolic;
  ans->pretext = StrBuf_string(pretext);
  ans->result = StrBuf_string(StrBuf_pruneNl(result));
  ans->posttext = StrBuf_string(posttext);
  ans->nextprompt = StrBuf_string(nextprompt);

  if (ans->posttext) {
    sscanf(ans->posttext," Time: %d ms",&time);
    sscanf(ans->posttext," Time: %*d ms plus GC time: %d ms",&gctime);
  }
  ans->time = time;
  ans->gctime = gctime;
  ans->error = (statcounter == -1 ? 1 : 0);

  RedMsg_cfprintf(debugfile,"<- RedAns_readUntilPrompt: leaving\n");

  return ans;
}

void RedAns_dfa(RedProc process,StrBuf *pstatcbuf,int *psymbolic,
		StrBuf *ppretext,StrBuf *presult,StrBuf *pposttext,
		StrBuf *pnextprompt) {
  unsigned char buffer[READBUFSIZE];
  int ncharread,ii;
  int status=PRETEXT,ch;

  RedMsg_cfprintf(debugfile,"-> RedAns_dfa: entering\n");
  RedMsg_cfprintf(debugfile,"-- RedAns_dfa: status=PRETEXT\n");

  while(status != FINISHED) {
    ncharread = read(process->reduceToMe[0],buffer,READBUFSIZE);
    for (ii=0; ii < ncharread; ii++) {
      ch = buffer[ii];
      if (ISCOLOR(ch)) {
	status = ch;
	RedAns_dfaLog(process,status);
      } else if (status == RESULT) {
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	//	if (ch >= 0x20)  /* in particular skip LF */
	if (ch >= 0x07)  /* skip prompt colorings */
	  *presult = StrBuf_addChar(*presult,ch);
      } else if (FASTMODE) {
	continue;
      } else if (status == STATCOUNTER) {
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	*pstatcbuf = StrBuf_addChar(*pstatcbuf,ch);
      } else if (status == PRETEXT) {
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	*ppretext = StrBuf_addChar(*ppretext,ch);
      } else if (status == MODE) {
	char chstr[2];
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	chstr[0] = ch;
	chstr[1] = 0;
	sscanf(chstr,"%d",psymbolic);
      } else if (status == POSTTEXT) {
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	if (ch >= 0x20)
	  *pposttext = StrBuf_addChar(*pposttext,ch);
      } else if (status == PROMPT) {
	RedMsg_cfprintf(process->rlgFile,"%c",ch);
	*pnextprompt = StrBuf_addChar(*pnextprompt,ch);
      }
    }
  }
  RedMsg_cfprintf(debugfile,"<- RedAns_dfa: leaving\n");
}

void RedAns_dfaLog(RedProc process,const int st) {
  if (process->rlgFile || debugfile) {
    const char *cTab[7]=COLORTAB;

    RedMsg_cfprintf(process->rlgFile,"<%s>",cTab[st]);
    RedMsg_cfprintf(debugfile,"-- RedAns_dfa: status=%s\n",cTab[st]);
  }
}

void RedAns_delete(RedAns ans) {
  free(ans->pretext);
  free(ans->result);
  free(ans->posttext);
  free(ans->nextprompt);
  free(ans);
}

void RedAns_cfprint(FILE *stream,RedAns ans) {
  if (stream) {
    fprintf(stream,"{int statcounter  = %d\n",ans->statcounter);
    fprintf(stream," int symbolic     = %d\n",ans->symbolic);
    fprintf(stream," char *pretext    = %s\n",ans->pretext);
    fprintf(stream," char *result     = %s\n",ans->result);
    fprintf(stream," char *posttext   = %s\n",ans->posttext);
    fprintf(stream," char *nextprompt = %s\n",ans->nextprompt);
    fprintf(stream," int time         = %d\n",ans->time);
    fprintf(stream," int gctime       = %d\n",ans->gctime);
    fprintf(stream," int error        = %d}\n",ans->error);
  }
}
