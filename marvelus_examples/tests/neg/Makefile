ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: letrec.zls
	$(ZELUC) $(ZFLAGS) letrec.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o letrec.opt letrec.ml main.ml

clean: 
	rm letrec.opt *.cmi *.cmx *.o *.zci main.ml letrec.ml 
