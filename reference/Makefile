OCAMLC ?= ocamlc
KERNEL := ../vendor/pts-dependent-types/reference
GENERATED := ../extraction/generated

.PHONY: all test clean
all: test

# The native algorithms run on the kernel's native reference; only this
# test compiles them together with the extract, to compare their answers
# and complete logs: algorithm 1 in diff.ml, algorithm 2 in
# diff_recursion.ml, both through the conversions of conversions.ml and
# the comparisons and counter of test_support.ml.
NATIVE := telescope_native.ml method_layout_native.ml diagnostics_native.ml common_native.ml registration_native.mli registration_native.ml elim_native.mli elim_native.ml recursion_native.mli recursion_native.ml
TESTS := data.ml programs.ml conversions.ml test_support.ml diff.ml diff_recursion.ml main.ml

# The extract and the kernel's files are copied into _build and compiled
# there as they are.  The files here are compiled where they are, so that
# errors point at them, into _build, with every warning an error except
# fragile matches (4), record patterns without [_] (9), type-directed
# disambiguation (40-42, 44, 45) and missing interfaces (70).
EXTERNAL := deptypes.mli deptypes.ml pts_native.mli pts_native.ml looping.ml constants.ml families.ml extracted.ml
WARNINGS := -w +A-4-9-40-41-42-44-45-70 -warn-error +A
OBJECTS := $(addprefix _build/,$(patsubst %.ml,%.cmo,$(filter %.ml,$(EXTERNAL) $(NATIVE) $(TESTS))))

# [_build/diff elim] or [_build/diff recursion] runs one of the suites.
test:
	$(MAKE) -C ../extraction extract
	mkdir -p _build
	cp $(GENERATED)/deptypes.ml $(GENERATED)/deptypes.mli _build/
	cp $(addprefix $(KERNEL)/,$(filter-out deptypes.%,$(EXTERNAL))) _build/
	cd _build && $(OCAMLC) -w -a -c $(EXTERNAL)
	for f in $(NATIVE) $(TESTS); do $(OCAMLC) $(WARNINGS) -I _build -c -o _build/$${f%.*} $$f || exit 1; done
	$(OCAMLC) $(OBJECTS) -o _build/diff
	_build/diff

clean:
	rm -rf _build
