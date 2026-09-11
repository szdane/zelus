ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: tuple.zls
	$(ZELUC) $(ZFLAGS) tuple.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o tuple.opt tuple.ml main.ml

clean: 
	rm -f tuple.opt *.cmi *.cmx *.o *.zci main.ml tuple.ml 
