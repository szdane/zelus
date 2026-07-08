ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 
sim: zelus-compile 


main.ml: watertank_delay.zls
	$(ZELUC) $(ZFLAGS) watertank_delay.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o watertank_delay.opt watertank_delay.ml main.ml

clean: 
	rm -f watertank_delay.opt *.cmi *.cmx *.o *.zci main.ml watertank_delay.ml 
