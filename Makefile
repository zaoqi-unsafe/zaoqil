SOURCES = eval.lisp

all: eval.rkt

eval.%: head.% $(SOURCES) tail.%
	> $@
	cat $^ >> $@


