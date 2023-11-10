DIRS=../../extraction \
  ../../lib \
	../../common \
	../../backend \
	../../cfrontend \
	../../cparser \
	../../driver \
	../../export \
	../../debug \
	../../riscV

INCLUDES=$(patsubst %,-I %,$(DIRS))

LIBS=str.cmxa

MAIN_OBJS:=$(shell ../../tools/modorder .depend test_backtranslation.cmx)

test_backtranslation: $(MAIN_OBJS)
	ocamlfind ocamlopt -package qcheck,menhirLib -linkpkg $(INCLUDES) -o test_backtranslation $(LIBS) $+

%.cmi: %.mli
	ocamlfind ocamlc -package qcheck,menhirLib -linkpkg $(INCLUDES) -c $<

%.cmo: %ml
	ocamlc $(INCLUDES) -c $<

%.cmx: %.ml
	ocamlfind ocamlopt -package qcheck,menhirLib -linkpkg $(INCLUDES) -c $<

depend:
	ocamlfind ocamldep $(INCLUDES) *.mli *.ml > .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.ml)) >> .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.mli)) >> .depend

include .depend

clean:
	-rm -f *.cm[ixo]
	-rm -f *.o
	-rm test_backtranslation