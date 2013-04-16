/* ---------------------------------------------------------------------
   $Id: RedProc.c 520 2010-01-01 19:42:30Z thomas-sturm $
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

#include <errno.h>

#include <string.h>

#include <sys/socket.h>

#include <fcntl.h>

#include <sys/ioctl.h>

#include <signal.h>

#if defined HAVE_WAIT_H
#include <wait.h>
#elif defined HAVE_SYS_WAIT_H
#include <sys/wait.h>
#endif

#include "reduce.h"
#include "StrBuf.h"
#include "RedAns.h"
#include "RedMsg.h"
#include "RedProc.h"

FILE *logfile=(FILE *)0;
FILE *debugfile=(FILE *)0;

static RedProc process;

RedProc RedProc_new(const char *reduce) {
  pid_t processId;

#ifdef LOGFILE
  if (!logfile) logfile = RedMsg_openLogfile("libreduce.log",logfile);
#endif
  
#ifdef DEBUG
  if (!debugfile) debugfile = stderr;
#endif
  
  process = (RedProc)malloc(sizeof(struct oRedProc));

  RedProc_initSockets(process);

  signal(SIGCHLD,RedProc_SigChld);
	
  (void)setsid();  /* become the leader of a new process group */

  if ((processId = fork())) {  /* I am not the child */
    
    if (processId < 0) {  /* failure */
      perror("libreduce: cannot fork()");
      exit(errno);
    }

    RedMsg_cfprintf(logfile,"successfully forked %d\n\n",processId);

    RedMsg_cfprintf(debugfile,
		    "-- reduce_init: parent process alive - fork()=%d\n",
		    processId);

    process->processId = processId;

    return RedProc_parent(process);
    
  } else {  /* I am the child */

    RedMsg_cfprintf(debugfile,
		    "-- reduce_init: child process alive - fork()=%d\n",
		    processId);

    RedProc_child(process,reduce);
  }

  return (RedProc)0;  /* just to make GCC happy */
}

void RedProc_initSockets(RedProc process) {
  if (USE_PIPES) {
    if (pipe(process->meToReduce) < 0) {
      perror("libreduce: failed to create pipe meToReduce\n");
      kill(process->processId,SIGTERM);
      exit(errno);
    }
    if (pipe(process->reduceToMe) < 0) {
      perror("libreduce: failed to create pipe reduceToMe\n");
      kill(process->processId,SIGTERM);
      exit(errno);
    }
  } else {
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, process->meToReduce) < 0) {
      perror("libreduce: failed to create pipe meToReduce\n");
      kill(process->processId,SIGTERM);
      exit(errno);
    }
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, process->reduceToMe) < 0) {
      perror("libreduce: failed to create pipe reduceToMe\n");
      kill(process->processId,SIGTERM);
      exit(errno);
    }
  }
}

RedProc RedProc_parent(RedProc process) {
#ifdef RLGFILE
  {
    char rlgFilename[32];
    
    sprintf(rlgFilename,"libreduce-%d.rlg",process->processId);
    process->rlgFile = RedMsg_openLogfile(rlgFilename,process->rlgFile);
  }
#else
  process->rlgFile = (FILE *)0;
#endif

  RedMsg_cfprintf(logfile,"created RedProc:\n");
  RedProc_cfprint(logfile,process);
  RedMsg_cfprintf(logfile,"\n");
  
  RedAns_loadInitFile(process);
  
  return process;
}

void RedProc_child(RedProc process,const char *reduce) {
  char *nargv[3];

  RedProc_removeSignalHandlers();  /* Just to make sure! */

  dup2(process->meToReduce[0],STDIN_FILENO);
  dup2(process->reduceToMe[1],STDOUT_FILENO);
  
  nargv[0] = (char *)reduce;
  nargv[1] = "-w";
  nargv[2] = (char *)0;
  
  RedMsg_cfprintf(debugfile,"-- RedProc_child: right before execv()\n");
  
  execv(nargv[0],nargv);

  {
    char errstr[1024];
    sprintf(errstr,"libreduce: cannot execv() %s",nargv[0]);
    perror(errstr); 
  }

  exit(errno);
}

void RedProc_delete(RedProc process) {
  pid_t pid=process->processId;

  RedMsg_cfprintf(logfile,"about to delete RedProc:\n");
  RedProc_cfprint(logfile,process);
  RedMsg_cfprintf(logfile,"\n");

  RedProc_kill(pid);

  if (process->rlgFile) fclose(process->rlgFile);

  free(process);
}

void RedProc_kill(pid_t pid) {
  pid_t waitres;
  int status;
  
  signal(SIGCHLD,SIG_DFL);

  RedMsg_cfprintf(debugfile,"\n-- reduce_finish: sending SIGKILL to %d\n",pid);

  kill(pid,SIGKILL);  /* I would be prefer SIGTERM but bpsl is not reliable */
  waitres = RedProc_waitPid(pid,&status);

  RedMsg_cfprintf(debugfile,
		  "-- reduce_finish: RedProc_waitPid returned %d\n", waitres);

  signal(SIGCHLD,RedProc_SigChld);

  RedMsg_cfprintf(debugfile,
		  "-- reduce_finish: successfully terminated %d\n",pid);
}

void RedProc_cfprint(FILE *stream,RedProc proc) {
  if (stream) {
    fprintf(stream,"{pid_t processId   = %d\n",proc->processId);
    fprintf(stream," int meToReduce[2] = {%d,%d}\n",
	    proc->meToReduce[0],proc->meToReduce[1]);
    fprintf(stream," int reduceToMe[2] = {%d,%d}\n",
	    proc->reduceToMe[0],proc->reduceToMe[1]);
    fprintf(stream," FILE *rlgFile     = %p}\n",proc->rlgFile);
  }
}

RETSIGTYPE RedProc_SigChld(int arg) {
  int status;
  
  //  fprintf(stderr,"libreduce: receiving SIGCHLD\n");
  if (wait4(process->processId,&status,WNOHANG,NULL) == process->processId) {
    fprintf(stderr,"libreduce: receiving SIGCHLD\n");
    fprintf(stderr,"libreduce: Reduce has stopped or exited - Quitting\n");
    exit(SIGCHLD);
  }
}

void RedProc_removeSignalHandlers(void) {
  signal(SIGQUIT,SIG_DFL);
  signal(SIGHUP,SIG_DFL);
  signal(SIGILL,SIG_DFL);
#ifndef LINUX
  signal(SIGBUS,SIG_DFL);
#endif
  signal(SIGSEGV,SIG_DFL);
  signal(SIGPIPE,SIG_DFL);
  signal(SIGCHLD,SIG_DFL);
  signal(SIGTERM,SIG_DFL);
}

pid_t RedProc_waitPid(pid_t pid,int *status) {
#if defined HAVE_WAIT4
#if defined HAVE_UNION_WAIT
  return wait4(pid,(union wait *)status,0,NULL);
#else
  return wait4(pid,status,0,NULL);
#endif
#elif defined HAVE_WAITPID
  return waitpid(pid,status,0);
#elif defined HAVE_WAIT3
#if defined HAVE_UNION_WAIT
  return wait3((union wait *)status,0,NULL);
#else
  return wait3(status,0,NULL);
#endif
#endif
}

void RedProc_error(RedProc process,const char *command,RedAns answer) {
  fprintf(stderr,"\n***** error in REDUCE ...\n\n");
  fprintf(stderr,"command = %s\n\n",command);
  RedAns_cfprint(stderr,answer);
}
