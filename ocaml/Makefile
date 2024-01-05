OCAMLC = ocamlc
OCAMLOPT = ocamlopt
OCAMLDEP = ocamldep
OCAMLDIR= ocamlc -where
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc

OCAMLFLAGS = 
OCAMLLIBS = unix.cma
OCAMLOPTLIBS = unix.cmxa

SRCS_PARSER = $(SRCS_YACC:.mly=.ml) $(SRCS_LEX:.mll=.ml)
SRCS_BYHAND = util.ml term.ml trs.ml bta.ml cnf.ml main.ml

SRCS = $(SRCS_BYHAND) $(SRCS_PARSER)
OBJS = $(SRCS:.ml=.cmo) 
OPTOBJS = $(SRCS:.ml=.cmx) 

all: ppl24

ppl24: depend $(OPTOBJS)
	$(OCAMLOPT) $(OCAMLFLAGS) $(OCAMLOPTLIBS) -o $@ $(OPTOBJS)

wc: $(SRCS_BYHAND)
	wc -l $^

depend: $(SRCS)
	$(OCAMLDEP) $^ > depend

-include depend

.SUFFIXES: .ml .mli .mly .mll .cmi .cmo .cmx

.ml.cmo: ; $(OCAMLC) $(OCAMLFLAGS) $(OCAMLLIBS) -c $<
.ml.cmx: ; $(OCAMLOPT) $(OCAMLFLAGS) $(OCAMLOPTLIBS) -c $<
.mli.cmi: ; $(OCAMLC) $(OCAMLFLAGS) $(OCAMLLIBS) -c $<

clean:
	rm -rf *~ *.cm* *.o *.a depend ppl24 \
	*.output $(SRCS_PARSER) $(SRCS_PARSER:.ml=.mli)
