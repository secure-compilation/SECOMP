include ../../Makefile.config

CCOMP=../../ccomp
CCOMPFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -fpic

all: main dylib.so

lib1.so: lib1.c
	$(CCOMP) $(CCOMPFLAGS) -shared -o $@ $<
lib2.so: lib2.c lib1.so
	$(CCOMP) $(CCOMPFLAGS) -shared -L. -o $@ $< -l1
dylib.so: dylib.c lib1.so
	$(CCOMP) $(CCOMPFLAGS) -shared -L. -o $@ $< -l1
main: main.c lib1.so lib2.so
	$(CCOMP) $(CCOMPFLAGS) -L. -o $@ main.c -l2 -l1

run: all
	LD_LIBRARY_PATH=. $(SIMU) ./main

test: all
	@if LD_LIBRARY_PATH=. $(SIMU) ./main | cmp -s - main.reference; \
         then echo "pic: passed"; \
         else echo "pic: FAILED"; exit 2; \
         fi

clean:
	rm -f *.o *.so main

