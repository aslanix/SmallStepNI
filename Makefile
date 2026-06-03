PREPROCESSDIR=doc_preprocess

.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	rocq makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

VS = $(wildcard *.v)

doc::
	for i in $(VS); do cat coqdoc.header $$i > $(PREPROCESSDIR)/$$i; done
	rocq doc -d doc -utf8 $(PREPROCESSDIR)/*.v

docclean:
	rm -rf $(PREPROCESSDIR)
	rm -rf doc/*
