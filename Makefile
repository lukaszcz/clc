
all: clc.vo

clc.vo : clc.v general.vo list_facts.vo basic_defs.vo iterms.vo lterms.vo sn.vo erase_facts.vo subterms.vo sred.vo red.vo standard.vo ired.vo icommute.vo svars.vo erasure.vo smred.vo icontr.vo istd.vo contraction.vo ared.vo sexpand.vo sexpand_std.vo acommute.vo astd.vo aexpand.vo expansion.vo central_lemma.vo aux.vo
	coqc clc.v

Reconstr.vo : Reconstr.v
	coqc Reconstr.v

general.vo : general.v Reconstr.vo
	coqc general.v

list_facts.vo : list_facts.v general.vo
	coqc list_facts.v

basic_defs.vo : basic_defs.v general.vo
	coqc basic_defs.v

iterms.vo : iterms.v basic_defs.vo general.vo
	coqc iterms.v

lterms.vo : lterms.v iterms.vo list_facts.vo general.vo
	coqc lterms.v

sn.vo : sn.v lterms.vo general.vo
	coqc sn.v

erase_facts.vo : erase_facts.v lterms.vo iterms.vo general.vo
	coqc erase_facts.v

erasure.vo : erasure.v lterms.vo iterms.vo list_facts.vo general.vo
	coqc erasure.v

subterms.vo : subterms.v lterms.vo iterms.vo general.vo
	coqc subterms.v

red.vo : red.v lterms.vo list_facts.vo general.vo
	coqc red.v

sred.vo : sred.v red.vo svars.vo subterms.vo sn.vo erase_facts.vo lterms.vo list_facts.vo general.vo
	coqc sred.v

standard.vo : standard.v sred.vo erasure.vo subterms.vo lterms.vo iterms.vo list_facts.vo general.vo
	coqc standard.v

svars.vo : svars.v erase_facts.vo lterms.vo iterms.vo list_facts.vo general.vo
	coqc svars.v

ired.vo : ired.v erase_facts.vo lterms.vo iterms.vo general.vo
	coqc ired.v

icommute.vo : icommute.v ired.vo sred.vo svars.vo erase_facts.vo lterms.vo iterms.vo general.vo
	coqc icommute.v

smred.vo : smred.v erasure.vo sred.vo sn.vo erase_facts.vo lterms.vo iterms.vo general.vo
	coqc smred.v

icontr.vo : icontr.v ired.vo sred.vo red.vo erasure.vo standard.vo subterms.vo erase_facts.vo lterms.vo iterms.vo general.vo
	coqc icontr.v

istd.vo : istd.v icommute.vo ired.vo sred.vo erasure.vo standard.vo subterms.vo erase_facts.vo lterms.vo iterms.vo general.vo
	coqc istd.v

contraction.vo : contraction.v istd.vo icontr.vo ired.vo sred.vo erasure.vo standard.vo lterms.vo iterms.vo general.vo
	coqc contraction.v

ared.vo : ared.v svars.vo sred.vo ired.vo standard.vo subterms.vo erase_facts.vo lterms.vo iterms.vo general.vo
	coqc ared.v

sexpand.vo : sexpand.v standard.vo subterms.vo erasure.vo lterms.vo iterms.vo list_facts.vo general.vo
	coqc sexpand.v

sexpand_std.vo : sexpand_std.v standard.vo subterms.vo lterms.vo basic_defs.vo general.vo
	coqc sexpand_std.v

acommute.vo : acommute.v sexpand_std.vo ared.vo sred.vo standard.vo subterms.vo svars.vo erase_facts.vo lterms.vo general.vo
	coqc acommute.v

astd.vo : astd.v acommute.vo sexpand_std.vo ared.vo sred.vo standard.vo subterms.vo erase_facts.vo lterms.vo basic_defs.vo list_facts.vo general.vo
	coqc astd.v

aexpand.vo : aexpand.v sexpand.vo ared.vo ired.vo sred.vo red.vo erasure.vo standard.vo subterms.vo lterms.vo iterms.vo general.vo
	coqc aexpand.v

expansion.vo : expansion.v astd.vo aexpand.vo acommute.vo istd.vo ired.vo ared.vo sred.vo erasure.vo standard.vo lterms.vo iterms.vo general.vo
	coqc expansion.v

central_lemma.vo : central_lemma.v smred.vo expansion.vo contraction.vo sred.vo erasure.vo standard.vo lterms.vo iterms.vo general.vo
	coqc central_lemma.v

aux.vo : aux.v central_lemma.vo iterms.vo general.vo
	coqc aux.v

clean:
	rm *.vo *.glob
