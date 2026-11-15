ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pi_param.zls
	$(ZELUC) $(ZFLAGS) pi_param.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pi_param.opt pi_param.ml main.ml

clean: 
	rm -f pi_param.opt *.cmi *.cmx *.o *.zci main.ml pi_param.ml 
