ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: oeitakeoff.zls
	$(ZELUC) $(ZFLAGS) oeitakeoff.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o oeitakeoff.opt oeitakeoff.ml main.ml

clean: 
	rm -f oeitakeoff.opt *.cmi *.cmx *.o *.zci main.ml oeitakeoff.ml 
