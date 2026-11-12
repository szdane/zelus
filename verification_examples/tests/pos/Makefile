ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: recursive02.zls
	$(ZELUC) $(ZFLAGS) recursive02.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o recursive02.opt recursive02.ml main.ml

clean: 
	rm recursive02.opt *.cmi *.cmx *.o *.zci main.ml recursive02.ml 
