ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: watertank01.zls
	$(ZELUC) $(ZFLAGS) watertank01.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o watertank01.opt watertank01.ml main.ml

clean: 
	rm -f watertank01.opt *.cmi *.cmx *.o *.zci main.ml watertank01.ml 
