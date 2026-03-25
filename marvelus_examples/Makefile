ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: reset.zls
	$(ZELUC) $(ZFLAGS) reset.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o reset.opt reset.ml main.ml

clean: 
	rm -f reset.opt *.cmi *.cmx *.o *.zci main.ml reset.ml 
