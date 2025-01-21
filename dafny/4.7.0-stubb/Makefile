 # -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

IDRIS2=idris2
DAFNY=dafny

TARGET_NAME := cs886
TARGET_OUT  := ${PWD}/__build/${TARGET_NAME}
TARGET      := ${TARGET_OUT}.dll

SOURCES := ${shell ls src/*.dfy}
MAIN := Main.dfy ConsoleIONative.cs
OPTS := --target cs -o cs886

# -- [ BUild ]

.PHONY: cs886-parse cs886-check cs886-audit cs886

cs886-parse: $(SOURCES)
	${MAKE} -C src DAFNY=${DAFNY} cs886-parse

cs886-check: $(SOURCES)
	${MAKE} -C src DAFNY=$(DAFNY) cs886-check

cs886-audit: $(SOURCES)
	${MAKE} -C src DAFNY=$(DAFNY) cs886-audit

cs886: $(SOURCES)
	mkdir -p __build
	${MAKE} -C src DAFNY=${DAFNY} TARGET=${TARGET_OUT} cs886

# -- [ Testing ]

.PHONY: cs886-test-build cs886-test-run cs886-test-run-re cs886-test-update

cs886-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

cs886-test-run:
	echo ${TARGET}
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

cs886-test-run-re:
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

cs886-test-update:
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 THREADS=1 \
			 ONLY=$(ONLY)


.PHONY: clobber clean

clean:
	${MAKE} -C tests clean

clobber: clean
	${MAKE} -C tests clobber
