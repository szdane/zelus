ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: water_tank.zls
	$(ZELUC) $(ZFLAGS) water_tank.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o water_tank.opt water_tank.ml main.ml

clean: 
	rm -f water_tank.opt *.cmi *.cmx *.o *.zci main.ml water_tank.ml 
