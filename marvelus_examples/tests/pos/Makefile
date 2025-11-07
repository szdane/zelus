ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: pos.zls
	$(ZELUC) $(ZFLAGS) pos.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pos.opt pos.ml main.ml

clean: 
	rm pos.opt *.cmi *.cmx *.o *.zci main.ml pos.ml 
