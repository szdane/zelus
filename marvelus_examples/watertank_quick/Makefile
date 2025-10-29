ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: watertank.zls
	$(ZELUC) $(ZFLAGS) watertank.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o watertank.opt watertank.ml main.ml

clean: 
	rm watertank.opt *.cmi *.cmx *.o *.zci main.ml watertank.ml 
