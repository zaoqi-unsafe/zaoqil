SOURCES = eval.lisp

all: eval.rkt eval.mal

eval.%: head*.% $(SOURCES) tail.%
	> $@
	cat $^ >> $@


