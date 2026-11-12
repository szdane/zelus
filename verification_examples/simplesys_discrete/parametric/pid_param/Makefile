ZELUC=zeluc
ZFLAGS= -verify -nodeadcode -s main
OCAMLFIND=ocamlfind
OCAMLOPT=ocamlopt
INCLUDE=-I /usr/local/include
CCLIB="-g `pkg-config --libs --cflags lcm`"
MLFLAGS=-linkpkg -package zelus 

sim: zelus-compile 

main.ml: pid_param.zls
	$(ZELUC) $(ZFLAGS) pid_param.zls

zelus-compile: main.ml
	$(OCAMLFIND) $(OCAMLOPT) $(MLFLAGS) -o pid_param.opt pid_param.ml main.ml

clean: 
	rm -f pid_param.opt *.cmi *.cmx *.o *.zci main.ml pid_param.ml 
