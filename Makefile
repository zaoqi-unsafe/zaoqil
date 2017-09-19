SOURCES = eval.lisp

all: eval.rkt eval.mal

eval.rkt: head.rkt $(SOURCES)
	cat $^ > $@

eval.mal: mal/scheme.mal mal/head.mal $(SOURCES) mal/tail.mal
	cat $^ > $@

