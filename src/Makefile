AGDA_BIN?=agda
AGDA_FLAGS?= -j10
SRC_DIR=.
AGDA_EXEC?=$(AGDA_BIN) $(AGDA_FLAGS)
# The heap cap is what turns a runaway term into a failed build rather than
# a dead desktop: GHC throws a heap-overflow at the limit, the kernel OOM
# killer does not.  Keep it well under total RAM -- the cap is per `agda`,
# and a second build (another checkout, an editor's Agda, an agent) is
# competing for the same memory.  16G against 31G of RAM and no swap is
# how the whole session gets killed instead of the one module.
RTS_HEAP?=8G
RTS_OPTIONS=+RTS -M$(RTS_HEAP) -RTS
AGDA=$(AGDA_EXEC) $(RTS_OPTIONS)

.PHONY : all
all : test

.PHONY : test
test : check

.PHONY : check
check:
	$(AGDA) --build-library

.PHONY : clean
clean:
	find $(SRC_DIR) -type f -name '*.agdai' -delete

.PHONY: debug
debug : ## Print debug information.
	@echo "AGDA_BIN              = $(AGDA_BIN)"
	@echo "AGDA_FLAGS            = $(AGDA_FLAGS)"
	@echo "AGDA_EXEC             = $(AGDA_EXEC)"
	@echo "AGDA                  = $(AGDA)"
	@echo "SRC_DIR               = $(SRC_DIR)"

# The stress suites, timed one at a time.  They are ordinary modules and
# `check` typechecks them along with everything else; this target exists to
# report the per-suite cost, which is the number a stress test is for.
#
# Every figure includes loading the interface files of the whole import
# stack -- ~13s on the machine this was written on.  That is what the
# `baseline` line measures: a module in the same stack with no test cases
# in it.  Subtract it, or better, compare figures across runs -- raise the
# size numerals inside a suite until the difference clears the noise, and
# the shape of that curve is the answer rather than any single number.
STRESS_BASELINE = Theory/Instances/Monoid/Pipeline/STLC.agda

STRESS_MODULES = \
  Theory/Instances/Monoid/Stress/Pipeline.agda \
  Theory/Instances/Monoid/Combinator/Decidable/ArithStress.agda \
  Theory/Instances/Monoid/Backreference/StressTests.agda

.PHONY: stress
stress:
	@for m in $(STRESS_BASELINE) $(STRESS_MODULES); do \
	  start=$$(date +%s%N); \
	  $(AGDA) $$m > /dev/null || exit 1; \
	  end=$$(date +%s%N); \
	  printf '%8d ms  %s\n' $$(( (end - start) / 1000000 )) $$m; \
	done
