ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pd_param.zls
	$(ZELUC) $(ZFLAGS) pd_param.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pd_param.opt pd_param.ml main.ml

clean: 
	rm -f pd_param.opt *.cmi *.cmx *.o *.zci main.ml pd_param.ml 
