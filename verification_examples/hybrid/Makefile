ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus

EXAMPLES= simple derivative_rule

.PHONY: sim all clean $(EXAMPLES)

sim: simple derivative_rule

all: $(EXAMPLES)

# Each example regenerates the shared main.ml, so always rebuild from scratch.
$(EXAMPLES):
	$(ZELUC) $(ZFLAGS) $@.zls
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o $@.opt $@.ml main.ml

clean:
	rm -f $(addsuffix .opt,$(EXAMPLES)) *.cmi *.cmx *.o *.zci main.ml $(addsuffix .ml,$(EXAMPLES))
