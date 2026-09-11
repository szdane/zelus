ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: cmsddtestint.zls
	$(ZELUC) $(ZFLAGS) cmsddtestint.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o cmsddtestint.opt cmsddtestint.ml main.ml

clean: 
	rm -f cmsddtestint.opt *.cmi *.cmx *.o *.zci main.ml cmsddtestint.ml 
