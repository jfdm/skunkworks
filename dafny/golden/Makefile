 # -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

IDRIS2=idris2
DAFNY=dafny

TARGET = ${CURDIR}/scooby

# -- [ BUild ]

scooby-parse: Scooby.dfy
	${DAFNY} resolve Scooby.dfy

scooby-check: Scooby.dfy
	${DAFNY} verify Scooby.dfy

scooby-audit: Scooby.dfy
	${DAFNY} audit Scooby.dfy

scooby: Scooby.dfy
	${DAFNY} build --target go Scooby.dfy -o scooby

# -- [ Testing ]

.PHONY: scooby-test-build scooby-test-run scooby-test-run-re scooby-test-update

scooby-test-build:
	${MAKE} -C tests testbin IDRIS2=$(IDRIS2)

scooby-test-run:
	echo ${TARGET}
	${MAKE} -C tests test \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 UPDATE='' \
			 ONLY=$(ONLY)

scooby-test-run-re:
	${MAKE} -C tests test-re \
			 IDRIS2=$(IDRIS2) \
			 PROG_BIN=$(TARGET) \
			 ONLY=$(ONLY)

scooby-test-update:
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
