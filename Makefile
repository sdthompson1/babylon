# Available make targets:
#
# Building:
#
#   `make`, `make all`, or `make release` -- build the compiler
#      executable as `build/babylon`
#
#   `make debug` -- build a debug executable as `build/babylon.debug`
#
#
# Demos/Examples:
#
#   `make chess` -- builds the chess demo (requires libsdl).
#
#   `make verify-chess` -- runs the verifier on the chess demo (in case
#      you want to see what running the verifier looks like). You'll
#      (probably) need all three of z3, cvc5 and vampire installed for
#      this to work properly.
#
#
# Cleaning:
#
#   `make clean` -- removes all files built by this Makefile.
#
#   `make mostlyclean` -- same as `make clean` except that
#      packages/*/build folders (created by `make packages`
#      or `make chess`) are left in place.
#
#
# Testing:
#
#   `make check` -- run the most important compiler self-tests.
#
#   `make check-valgrind` -- runs the same tests that `make check` would,
#      but using Valgrind. This checks for memory leaks but is somewhat
#      slower than `make check`.
#
#   `make packages` -- builds and verifies all Babylon packages
#      present in the `packages` folder. Requires libsdl2. Slow.
#
#   `make check-all` -- runs all of `make check`, `make check-valgrind`
#      and `make packages`. Very slow, but worth running occasionally
#      (e.g. before a major release) -- preferably with a `make clean`
#      beforehand -- to make sure everything still builds and works
#      properly.
#
#   (There are other options for finer-grained testing e.g.
#   `make main-tests filter=Quantifiers` or `make sequence-tests` etc.
#   Read the code for more details, especially the makefile rules below
#   and the test/run_tests.sh script.)
#
#
# Coverage Checks:
#
#   `make cover` -- build the compiler in coverage mode (creating
#      output `build/babylon.coverage`) and run the same tests that
#      `make check` would, but in coverage mode. Requires gcov installed.
#      Test coverage statistics will be printed to stdout and detailed
#      results will appear in the `gcov` directory.
#
#   `make incr-cover` -- Incremental coverage. Re-runs tests and
#      adds results to existing coverage stats. `flags` may be used,
#      e.g. `make incr-coverage flags="-m -f Arith" will re-run only
#      "main tests" with Arith in their name.


# Compiler settings
CC := gcc
CFLAGS := -std=c11 -pedantic -Wall -Wextra -Wno-unused-parameter -Werror -MMD -MP
DEBUG_CFLAGS := -g
RELEASE_CFLAGS := -O3
COVERAGE_CFLAGS := --coverage
LIBS := -lsqlite3

# Output binary name
DEBUG_EXE := build/babylon.debug
RELEASE_EXE := build/babylon
COVERAGE_EXE := build/babylon.coverage

# File patterns
SRCS := $(wildcard src/*.c)
DEBUG_OBJS := $(patsubst src/%.c,build/debug/%.o,$(SRCS))
RELEASE_OBJS := $(patsubst src/%.c,build/release/%.o,$(SRCS))
COVERAGE_OBJS := $(patsubst src/%.c,build/coverage/%.o,$(SRCS))
DEPS := $(patsubst src/%.c,build/deps/%.d,$(SRCS))

# Phony targets
.PHONY: all debug release cover incr-cover \
	mostlyclean clean \
	check check-valgrind check-all test test-valgrind test-all \
	main-tests main-tests-valgrind \
	sequence-tests sequence-tests-valgrind \
	package-tests package-tests-valgrind \
	packages \
	chess verify-chess

# Default build
all: release

# Include dependency files if they exist
-include $(DEPS)


#
# Debug Rules
#
debug: $(DEBUG_EXE)

$(DEBUG_EXE): $(DEBUG_OBJS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(DEBUG_CFLAGS) $(DEBUG_OBJS) $(LIBS) -o $(DEBUG_EXE)

build/debug/%.o: src/%.c
	@mkdir -p $(@D)
	@mkdir -p build/deps
	$(CC) $(CFLAGS) -MF $(patsubst src/%.c,build/deps/%.d,$<) $(DEBUG_CFLAGS) -c $< -o $@


#
# Release Rules
#
release: $(RELEASE_EXE)

$(RELEASE_EXE): $(RELEASE_OBJS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(RELEASE_CFLAGS) $(RELEASE_OBJS) $(LIBS) -o $(RELEASE_EXE)

build/release/%.o: src/%.c
	@mkdir -p $(@D)
	@mkdir -p build/deps
	$(CC) $(CFLAGS) -MF $(patsubst src/%.c,build/deps/%.d,$<) $(RELEASE_CFLAGS) -c $< -o $@


#
# Coverage Rules
#
cover: $(COVERAGE_EXE)
	rm -fr gcov
	mkdir -p gcov/build
	ln -sf ../test gcov/
	ln -sf ../src gcov/
	cd gcov; ./test/run_tests.sh -c ../build/babylon.coverage -msp
	cd gcov; gcov -o ../build/coverage ../src/*.c

incr-cover: $(COVERAGE_EXE)
	cd gcov; ./test/run_tests.sh -c ../build/babylon.coverage $(flags)
	cd gcov; gcov -o ../build/coverage ../src/*.c

$(COVERAGE_EXE): $(COVERAGE_OBJS)
	@mkdir -p $(@D)
	$(CC) $(CFLAGS) $(COVERAGE_CFLAGS) $(COVERAGE_OBJS) $(LIBS) -o $(COVERAGE_EXE)

build/coverage/%.o: src/%.c
	@mkdir -p $(@D)
	@mkdir -p build/deps
	$(CC) $(CFLAGS) -MF $(patsubst src/%.c,build/deps/%.d,$<) $(COVERAGE_CFLAGS) -c $< -o $@



#
# Clean Rules
#
mostlyclean:
	rm -rf build gcov test/output_tmp

clean: mostlyclean
	rm -rf packages/*/build


#
# Tests
#

check: main-tests sequence-tests package-tests
	@echo "All tests passed!"

check-valgrind: main-tests-valgrind sequence-tests-valgrind package-tests-valgrind

check-all: check check-valgrind packages
	@echo "All tests passed!"

# 'test' is a synonym for 'check'
test: check
test-valgrind: check-valgrind
test-all: check-all


# Rules for running subsets of the tests:
main-tests: $(RELEASE_EXE)
	test/run_tests.sh -m $(filter)

main-tests-valgrind: $(RELEASE_EXE)
	test/run_tests.sh -vm $(filter)

sequence-tests: $(RELEASE_EXE)
	test/run_tests.sh -s

sequence-tests-valgrind: $(RELEASE_EXE)
	test/run_tests.sh -vs

package-tests: $(RELEASE_EXE)
	test/run_tests.sh -p

package-tests-valgrind: $(RELEASE_EXE)
	test/run_tests.sh -vp

packages: $(RELEASE_EXE)
	cd packages; ./verify_packages.sh


#
# Chess Example
#

chess: $(RELEASE_EXE)
	cd packages; ../$(RELEASE_EXE) -c -p . -r chess
	@echo "Build successful!"
	@echo "To run the chess example, cd into packages/chess"
	@echo "and then type: ./build/bin/chess"

verify-chess: $(RELEASE_EXE)
	cd packages; ../$(RELEASE_EXE) -v -p . -r chess
