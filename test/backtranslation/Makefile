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

PACKAGES=qcheck,menhirLib

MAIN_OBJS:=$(shell ../../tools/modorder .depend test_backtranslation.cmx)

test_backtranslation: $(MAIN_OBJS)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg $(INCLUDES) -o test_backtranslation $(LIBS) $+

test_backtranslation.byte: $(MAIN_OBJS:.cmx=.cmo)
	ocamlfind ocamlc -g -package $(PACKAGES) -linkpkg $(INCLUDES) -o test_backtranslation.byte $(LIBS:.cmxa=.cma) $+

# Regression test that the output of the back-translation compiles, see
# test_compiles.ml.  It does not need QCheck.
TEST_COMPILES_OBJS:=$(shell ../../tools/modorder .depend test_compiles.cmx)

# If .depend does not list test_compiles.cmx, because it is empty or was
# generated before test_compiles.ml existed, or if ../../tools/modorder does
# not exist because CompCert is not built, the link would succeed with no
# modules and the test would silently check nothing.  If .depend is missing,
# this check also gives a clearer message than the include below.
ifneq ($(filter test_compiles run_test_compiles,$(MAKECMDGOALS)),)
ifeq ($(filter test_compiles.cmx,$(TEST_COMPILES_OBJS)),)
$(error ../../tools/modorder found no test_compiles.cmx in .depend: build CompCert first, then run touch .depend and make depend)
endif
endif

test_compiles: PACKAGES=menhirLib
test_compiles: LIBS=str.cmxa unix.cmxa
test_compiles: $(TEST_COMPILES_OBJS)
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg $(INCLUDES) -o test_compiles $(LIBS) $+

run_test_compiles: test_compiles
	COMPCERT_CONFIG=../../compcert.ini ./test_compiles

.PHONY: run_test_compiles

%.cmi: %.mli
	ocamlfind ocamlc -package $(PACKAGES) -linkpkg $(INCLUDES) -c $<

%.cmo: %.ml
	ocamlfind ocamlc -g -package $(PACKAGES) -linkpkg $(INCLUDES) -c $<

%.cmx: %.ml
	ocamlfind ocamlopt -package $(PACKAGES) -linkpkg $(INCLUDES) -c $<

depend:
	ocamlfind ocamldep $(INCLUDES) *.mli *.ml > .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.ml)) >> .depend
	ocamlfind ocamldep $(INCLUDES) $(foreach d,$(DIRS),$(wildcard $(d)/*.mli)) >> .depend

include .depend

clean:
	-@rm -f *.cm[ixo] 2>/dev/null || true
	-@rm -f *.o 2>/dev/null || true
	-@rm test_backtranslation 2>/dev/null || true
	-@rm test_backtranslation.byte 2>/dev/null || true
	-@rm test_compiles 2>/dev/null || true
