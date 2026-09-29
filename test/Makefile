include ../Makefile.config

DIRS=c compression raytracer spass regression abi
ifeq ($(PIC_SUPPORTED),true)
DIRS+=pic
endif
ifeq ($(CLIGHTGEN),true)
DIRS+=export
endif

all:
	set -e; for i in $(DIRS); do $(MAKE) CCOMPOPTS='$(CCOMPOPTS)' -C $$i all; done

all_s:
	set -e; for i in $(DIRS); do $(MAKE) CCOMPOPTS='$(CCOMPOPTS)' -C $$i all_s; done

test:
	set -e; for i in $(DIRS); do $(MAKE) SIMU='$(SIMU)' -C $$i test; done

parallel:
	parallel $(MAKE) SIMU='$(SIMU)' -C {} test ::: $(DIRS)

bench:
	for i in $(DIRS); do $(MAKE) -C $$i bench; done

clean:
	for i in $(DIRS); do $(MAKE) -C $$i clean; done
