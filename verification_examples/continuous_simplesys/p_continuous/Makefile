ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: p_continuous.zls
	$(ZELUC) $(ZFLAGS) p_continuous.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o p_continuous.opt p_continuous.ml main.ml

clean: 
	rm -f p_continuous.opt *.cmi *.cmx *.o *.zci main.ml p_continuous.ml 
