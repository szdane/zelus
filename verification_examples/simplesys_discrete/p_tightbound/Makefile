ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: p_tightbound.zls
	$(ZELUC) $(ZFLAGS) p_tightbound.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o p_tightbound.opt p_tightbound.ml main.ml

clean: 
	rm -f p_tightbound.opt *.cmi *.cmx *.o *.zci main.ml p_tightbound.ml 
