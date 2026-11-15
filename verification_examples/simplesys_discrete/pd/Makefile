ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pd.zls
	$(ZELUC) $(ZFLAGS) pd.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pd.opt pd.ml main.ml

clean: 
	rm -f pd.opt *.cmi *.cmx *.o *.zci main.ml pd.ml 
