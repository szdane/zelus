ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pi.zls
	$(ZELUC) $(ZFLAGS) pi.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pi.opt pi.ml main.ml

clean: 
	rm -f pi.opt *.cmi *.cmx *.o *.zci main.ml pi.ml 
