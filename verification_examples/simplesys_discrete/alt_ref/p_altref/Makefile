ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: p_altref.zls
	$(ZELUC) $(ZFLAGS) p_altref.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o p_altref.opt p_altref.ml main.ml

clean: 
	rm -f p_altref.opt *.cmi *.cmx *.o *.zci main.ml p_altref.ml 
