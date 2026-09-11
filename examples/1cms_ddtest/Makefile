ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: cmsddtest.zls
	$(ZELUC) $(ZFLAGS) cmsddtest.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o cmsddtest.opt cmsddtest.ml main.ml

clean: 
	rm -f cmsddtest.opt *.cmi *.cmx *.o *.zci main.ml cmsddtest.ml 
