ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: automaton.zls
	$(ZELUC) $(ZFLAGS) automaton.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o automaton.opt automaton.ml main.ml

clean: 
	rm -f automaton.opt *.cmi *.cmx *.o *.zci main.ml automaton.ml 
