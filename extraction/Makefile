COQC ?= coqc
DUNE ?= dune
KERNEL := ../vendor/pts-dependent-types

.PHONY: all core extract run test clean
all: run

core:
	$(MAKE) -C .. rocq

# Extract.v writes generated/deptypes.ml; the kernel's printer is copied
# next to it unchanged.
extract: core
	mkdir -p generated
	$(COQC) -Q $(KERNEL)/theories DepTypes -Q ../theories IndTypes Extract.v
	cp $(KERNEL)/extraction/pretty.ml generated/

run: extract
	$(DUNE) exec ./main.exe

test: extract
	$(DUNE) test

clean:
	rm -rf generated *.vo *.vos *.vok *.glob .*.aux
	$(DUNE) clean
