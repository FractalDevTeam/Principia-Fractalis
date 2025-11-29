COQC = coqc
COQDEP = coqdep
COQFLAGS = -Q theories PF_Coq

VFILES = $(shell cat _CoqProject | grep '\.v$$')
VOFILES = $(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) $(COQFLAGS) $<

depend:
	$(COQDEP) $(COQFLAGS) $(VFILES) > .depend

clean:
	rm -f theories/*/*.vo theories/*/*.vok theories/*/*.vos theories/*/*.glob
	rm -f theories/*.vo theories/*.vok theories/*.vos theories/*.glob
	rm -f .depend

.PHONY: all depend clean

-include .depend
