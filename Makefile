OBJS = syntax.cmo print.cmo metric.cmo eval.cmo typecheck.cmo

all: $(OBJS)

include .depend

# Build an executable typechecker
# f: $(OBJS) main.cmo 
# 	@echo Linking $@
# 	ocamlc -o $@ $(OBJS) 

# Compile an ML module interface
%.cmi : %.mli
	ocamlc -c $<

# Compile an ML module implementation
%.cmo : %.ml
	ocamlc -c $<

# Clean up the directory
clean::
	rm -rf *.cm[io] 

# Rebuild intermodule dependencies
depend:: 
	ocamldep *.mli *.ml > .depend