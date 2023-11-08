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

MAIN_OBJS:=$(shell ../../tools/modorder .depend main.cmx)

main: $(MAIN_OBJS)
	ocamlfind ocamlopt -package qcheck -linkpkg $(INCLUDES) -o main $(LIBS) $+

%.cmi: %.mli
	ocamlfind ocamlc -package qcheck $(INCLUDES) -c $<

%.cmo: %ml
	ocamlc $(INCLUDES) -c $<

%.cmx: %.ml
	ocamlfind ocamlopt -package qcheck $(INCLUDES) -c $<

depend:
	ocamlfind ocamldep $(INCLUDES) *.mli *.ml > .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.ml)) >> .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.mli)) >> .depend

include .depend

clean:
	-rm -f *.cm[ix]
	-rm -f main.o