TESTS = $(wildcard test/*.lean)

.PHONY: all build test

all: build test

build:
	lake build

test: $(addsuffix .run, $(TESTS))

test/%.run: build
	env LEAN_PATH=build/lib lean test/$*
