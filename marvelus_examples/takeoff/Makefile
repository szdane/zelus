ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: takeoff.zls
	$(ZELUC) $(ZFLAGS) takeoff.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o takeoff.opt takeoff.ml main.ml

clean: 
	rm -f takeoff.opt *.cmi *.cmx *.o *.zci main.ml takeoff.ml 
