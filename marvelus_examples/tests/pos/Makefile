ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: ite01.zls
	$(ZELUC) $(ZFLAGS) ite01.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o ite01.opt ite01.ml main.ml

clean: 
	rm ite01.opt *.cmi *.cmx *.o *.zci main.ml ite01.ml 
