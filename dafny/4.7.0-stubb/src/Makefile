# -- [ Makefile ]
#
# Makefile for the project.
#
# -- [ EOH ]

DAFNY=dafny

TARGET := cs886

SOURCES := ${shell ls *.dfy}

MAIN := Main.dfy

MAIN_PLUS := ${MAIN} ConsoleIO.dfy ConsoleIONative.cs

OPTS := --target cs --output $(TARGET)

# -- [ BUild ]

.PHONY: cs886-parse cs886-check cs886-audit cs886

cs886-parse: $(SOURCES)
	${DAFNY} resolve $(MAIN)

cs886-check: $(SOURCES)
	${DAFNY} verify $(MAIN)

cs886-audit: $(SOURCES)
	${DAFNY} audit $(MAIN)

cs886: $(SOURCES)
	${DAFNY} build $(MAIN_PLUS) $(OPTS)

.PHONY: clean

clean:
	find -iname "*~" -delete

# -- [ EOF ]
