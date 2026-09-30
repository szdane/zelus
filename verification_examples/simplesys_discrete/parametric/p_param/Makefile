ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: p_param.zls
	$(ZELUC) $(ZFLAGS) p_param.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o p_param.opt p_param.ml main.ml

clean: 
	rm -f p_param.opt *.cmi *.cmx *.o *.zci main.ml p_param.ml 
