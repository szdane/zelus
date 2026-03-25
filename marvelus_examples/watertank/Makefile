ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: wt02.zls
	$(ZELUC) $(ZFLAGS) wt02.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o wt02.opt wt02.ml main.ml

clean: 
	rm -f wt02.opt *.cmi *.cmx *.o *.zci main.ml wt02.ml 
