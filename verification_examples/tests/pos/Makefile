ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: automaton01.zls
	$(ZELUC) $(ZFLAGS) automaton01.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o automaton01.opt automaton01.ml main.ml

clean: 
	rm automaton01.opt *.cmi *.cmx *.o *.zci main.ml automaton01.ml 
