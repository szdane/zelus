ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: practice.zls
	$(ZELUC) $(ZFLAGS) practice.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o practice.opt practice.ml main.ml

clean: 
	rm -f practice.opt *.cmi *.cmx *.o *.zci main.ml practice.ml 
