ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: cmscc.zls
	$(ZELUC) $(ZFLAGS) cmscc.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o cmscc.opt cmscc.ml main.ml

clean: 
	rm -f cmscc.opt *.cmi *.cmx *.o *.zci main.ml cmscc.ml 
