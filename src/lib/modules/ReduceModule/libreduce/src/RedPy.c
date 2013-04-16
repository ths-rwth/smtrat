#include <Python.h>
#include <string.h>
#include "reduce.h"
#include "RedMsg.h"

extern FILE *debugfile;

static PyObject *RedPy_procNew(PyObject *self, PyObject *args) {
  char *fromPython;
  RedProc p;
  PyObject *tmp;

  RedMsg_cfprintf(debugfile,"-> in RedPy:procNew\n");
  if (!PyArg_Parse(args,"(s)",&fromPython))
    return NULL;
  RedMsg_cfprintf(debugfile,"after Parse: %s\n",fromPython);
  p = RedProc_new(fromPython);
  RedMsg_cfprintf(debugfile,"after new: %lld",p);
  RedProc_cfprint(debugfile,p);
  tmp = Py_BuildValue("{sKsK}}",
		      "processId",
		      p->processId,
		      "handle",
		      p);
  return tmp;
}

static PyObject *RedPy_procDelete(PyObject *self, PyObject *args) {
  RedProc p;

  if (! PyArg_Parse(args,"(K)",&p))
    return NULL;
  RedProc_delete(p);
  return Py_BuildValue("");
}

static PyObject *RedPy_ansNew(PyObject *self, PyObject *args) {
  RedProc p;
  char *fromPython;
  RedAns ans;

  if (!PyArg_Parse(args,"(Ks)",&p,&fromPython))
    return NULL;
  Py_BEGIN_ALLOW_THREADS
  ans = RedAns_new(p,fromPython);
  Py_END_ALLOW_THREADS
  return Py_BuildValue("{s{sisisssssssssisisi}sK}})",
		       "data",
		       "statcounter",ans->statcounter,
		       "symbolic",ans->symbolic,
		       "pretext",ans->pretext,
		       "result",ans->result,
		       "posttext",ans->posttext,
		       "nextpompt",ans->nextprompt,
		       "time",ans->time,
		       "gctime",ans->gctime,
		       "error",ans->error,
		       "handle",ans);
}

static PyObject *RedPy_ansDelete(PyObject *self, PyObject *args) {
  RedAns ans;

  if (!PyArg_Parse(args,"(K)",&ans))
    return NULL;
  RedAns_delete(ans);
  return Py_BuildValue("");
}

static struct PyMethodDef RedPy_methods[] = {
    {"procNew", RedPy_procNew, METH_VARARGS},
    {"procDelete", RedPy_procDelete, METH_VARARGS},
    {"ansNew", RedPy_ansNew, METH_VARARGS},
    {"ansDelete", RedPy_ansDelete, METH_VARARGS},
    {NULL, NULL}
};

/* module initializer */
void initRedPy() {
  (void)Py_InitModule("RedPy", RedPy_methods);
}
