OCAMLC ?= ocamlc
KERNEL := ../vendor/pts-dependent-types/reference

.PHONY: all test clean
all: test

# The native algorithms run on the kernel's native reference; only this
# test compiles them together with the extract, to compare their answers
# and complete logs: algorithm 1 in diff.ml, algorithm 2 in
# diff_recursion.ml, which reuses its conversions.
NATIVE := diagnostics_native.ml elim_native.mli elim_native.ml recursion_native.mli recursion_native.ml
TESTS := data.ml programs.ml diff.ml diff_recursion.ml

test:
	$(MAKE) -C ../extraction extract
	mkdir -p _build
	cp ../extraction/generated/deptypes.ml ../extraction/generated/deptypes.mli _build/
	cp $(KERNEL)/pts_native.mli $(KERNEL)/pts_native.ml $(KERNEL)/looping.ml $(KERNEL)/constants.ml $(KERNEL)/families.ml $(KERNEL)/extracted.ml _build/
	cp $(NATIVE) $(TESTS) _build/
	cd _build && $(OCAMLC) deptypes.mli deptypes.ml pts_native.mli pts_native.ml looping.ml constants.ml families.ml extracted.ml $(NATIVE) $(TESTS) -o diff
	_build/diff

clean:
	rm -rf _build
