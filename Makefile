COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) all

install: $(COQMAKEFILE)
	+$(MAKE) -f $(COQMAKEFILE) install

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	test ! -f $(COQMAKEFILE) || $(MAKE) -f $(COQMAKEFILE) cleanall
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

.PHONY: all install clean
