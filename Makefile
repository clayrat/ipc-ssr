OCAMLBUILD = ocamlbuild -tag safe_string -pkg zarith -I src

default: Makefile.coq
	+$(MAKE) -f Makefile.coq

benchmark: default
	$(OCAMLBUILD) benchmark.native

clean: Makefile.coq
	+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf src/search.ml src/search.mli
	$(OCAMLBUILD) -clean

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject Makefile: ;

%: Makefile.coq
	+$(MAKE) -f Makefile.coq $@

.PHONY: default benchmark clean
