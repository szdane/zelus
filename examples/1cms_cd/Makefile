ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: cmscd.zls
	$(ZELUC) $(ZFLAGS) cmscd.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o cmscd.opt cmscd.ml main.ml

clean: 
	rm -f cmscd.opt *.cmi *.cmx *.o *.zci main.ml cmscd.ml 
