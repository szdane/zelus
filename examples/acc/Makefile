ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: acc_1car.zls
	$(ZELUC) $(ZFLAGS) acc_1car.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o acc_1car.opt acc_1car.ml main.ml

clean: 
	rm -f acc_1car.opt *.cmi *.cmx *.o *.zci main.ml acc_1car.ml 
