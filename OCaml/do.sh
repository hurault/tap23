#!/bin/bash

case $1 in

  "clean")
   rm a.out *.cmx *.cmi *.o *.cmo runAXpCXp
    ;;

  "compil")
  ocamlopt dataset.ml
  ocamlfind ocamlopt -package pyml -linkpkg dataset.cmx explain.ml
  ocamlfind ocamlopt -package pyml -linkpkg dataset.cmx explain.cmx runAXpCXp.ml -o runAXpCXp
  ocamlopt unix.cmxa dataset.cmx analyseAXpCXp.ml -o analyseAXpCXp
    ;;

  *) 
esac
