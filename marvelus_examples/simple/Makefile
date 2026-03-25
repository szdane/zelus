ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: simple.zls
	$(ZELUC) $(ZFLAGS) simple.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o simple.opt simple.ml main.ml

clean: 
	rm -f simple.opt *.cmi *.cmx *.o *.zci main.ml simple.ml 
