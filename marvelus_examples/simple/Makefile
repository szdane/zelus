ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: recursive.zls
	$(ZELUC) $(ZFLAGS) recursive.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o recursive.opt recursive.ml main.ml

clean: 
	rm -f recursive.opt *.cmi *.cmx *.o *.zci main.ml recursive.ml 
