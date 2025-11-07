ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: func.zls
	$(ZELUC) $(ZFLAGS) func.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o func.opt func.ml main.ml

clean: 
	rm func.opt *.cmi *.cmx *.o *.zci main.ml func.ml 
