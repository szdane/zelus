ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: cmsdd.zls
	$(ZELUC) $(ZFLAGS) cmsdd.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o cmsdd.opt cmsdd.ml main.ml

clean: 
	rm -f cmsdd.opt *.cmi *.cmx *.o *.zci main.ml cmsdd.ml 
