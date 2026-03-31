# ----- Config -----
POS_DIR := pos
NEG_DIR := neg

ZELUC      := zeluc
ZFLAGS     := -verify -nodeadcode -s main

OCAMLFIND  := ocamlfind
OCAMLOPT   := ocamlopt
OCAMLDBG   := -g
MLFLAGS    := -linkpkg -package zelus

# Optional include / external C libs (safe if missing)
INCLUDE    := -I /usr/local/include
LCM_CFLAGS := $(shell pkg-config --cflags lcm 2>/dev/null)
LCM_LIBS   := $(shell pkg-config --libs   lcm 2>/dev/null)

# Only treat files matching this glob as tests
TEST_GLOB ?= *.zls

# ----- Discover tests -----
POS_ZLS := $(wildcard $(POS_DIR)/$(TEST_GLOB))
NEG_ZLS := $(wildcard $(NEG_DIR)/$(TEST_GLOB))

# Map .zls -> .opt (build outputs)
POS_BINS := $(patsubst %.zls,%.opt,$(POS_ZLS))
NEG_BINS := $(patsubst %.zls,%.opt,$(NEG_ZLS))

# zeluc generates files like main.ml; avoid parallel compile
.NOTPARALLEL:
.SHELLFLAGS := -eu -o pipefail -c

.PHONY: all build list verify verify-pos verify-neg clean

# ----- Introspection (optional) -----
list:
	@echo "POS_ZLS: $(POS_ZLS)"
	@echo "NEG_ZLS: $(NEG_ZLS)"
	@echo "POS_BINS: $(POS_BINS)"
	@echo "NEG_BINS: $(NEG_BINS)"

# ----- Build everything (.opt only; do not run them) -----
all: build
build: $(POS_BINS) $(NEG_BINS)

# Generic build rule:
#   pos/foo_test.zls -> pos/foo_test.opt   (build happens inside its dir)
%.opt: %.zls
	@set -e; d=$(@D); base=$(*F); \
	echo "==> Compiling $$d/$$base.zls -> $$d/$$base.opt"; \
	cd "$$d" && \
	$(ZELUC) $(ZFLAGS) "$$base.zls" && \
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) $(OCAMLDBG) \
	  $(INCLUDE) \
	  $(if $(LCM_CFLAGS),-ccopt '$(LCM_CFLAGS)') \
	  $(if $(LCM_LIBS),  -cclib '$(LCM_LIBS)') \
	  -o "$$base.opt" "$$base.ml" main.ml

# ----- Verify (use zeluc only; do NOT run .opt) -----
sim: sim-pos sim-neg

# Positive suite: pass if zeluc exits 0
sim-pos:
	@total=0; passed=0; \
	if [ -z "$(POS_ZLS)" ]; then \
	  echo ""; echo "$(POS_DIR): 0 tests run, 0 passed."; \
	else \
	  for z in $(POS_ZLS); do \
	    d=$$(dirname "$$z"); f=$$(basename "$$z"); \
	    echo "==> Verifying $$z"; \
	    if (cd "$$d" && $(ZELUC) $(ZFLAGS) "$$f" $(if $(VERBOSE),,>/dev/null 2>&1)); then \
	      echo "-- PASS: $$z"; passed=$$((passed+1)); \
	    else \
	      s=$$?; echo "-- FAIL: $$z [status=$$s]"; \
	    fi; \
	    total=$$((total+1)); \
	  done; \
	  echo ""; echo "$(POS_DIR): $$total tests run, $$passed passed."; \
	fi

# Negative suite: pass if zeluc fails (non-zero)
sim-neg:
	@total=0; passed=0; \
	if [ -z "$(NEG_ZLS)" ]; then \
	  echo ""; echo "$(NEG_DIR): 0 tests run, 0 passed."; \
	else \
	  for z in $(NEG_ZLS); do \
	    d=$$(dirname "$$z"); f=$$(basename "$$z"); \
	    echo "==> Verifying $$z"; \
	    if (cd "$$d" && $(ZELUC) $(ZFLAGS) "$$f" $(if $(VERBOSE),,>/dev/null 2>&1)); then \
	      echo "-- FAIL (unexpected success): $$z"; \
	    else \
	      s=$$?; echo "-- PASS (failed as expected): $$z [status=$$s]"; passed=$$((passed+1)); \
	    fi; \
	    total=$$((total+1)); \
	  done; \
	  echo ""; echo "$(NEG_DIR): $$total tests run, $$passed passed."; \
	fi

# ----- Clean -----
clean:
	@echo "Cleaning generated files..."
	@for d in "$(POS_DIR)" "$(NEG_DIR)"; do \
	  [ -d $$d ] || continue; \
	  rm -f $$d/*.opt $$d/*.ml $$d/*.cmi $$d/*.cmx $$d/*.o $$d/*.zci $$d/main.ml; \
	done
	@rm -f main.ml 2>/dev/null || true
