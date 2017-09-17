SOURCES = eval.lisp

eval.rkt: head.rkt $(SOURCES)
	cat $< > $@
	cat $(SOURCES) >> $@
