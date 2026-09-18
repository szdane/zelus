ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pid.zls
	$(ZELUC) $(ZFLAGS) pid.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pid.opt pid.ml main.ml

clean: 
	rm -f pid.opt *.cmi *.cmx *.o *.zci main.ml pid.ml 
