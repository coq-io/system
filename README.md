# ![Logo](https://raw.githubusercontent.com/clarus/icons/master/megaphone-48.png) IO System
> Library of Unix effects for Coq. See also [Coq.io](http://coq.io/).

    Require Import Io.All.
    Require Import Io.System.All.
    Require Import ListString.All.

    Import C.Notations.

    Definition hello_world (argv : list LString.t) : C.t System.effect unit :=
      System.log (LString.s "Hello world!").

## Install
Using [OPAM for Coq](coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq-io-system

## Documentation
See http://coq.io/.

## Extraction
To run a program you can extract it to [OCaml](https://ocaml.org/). Do:

    Definition main := Extraction.launch hello_world.
    Extraction "main" main.

You can now compile and execute `main.ml`:

    ocamlbuild main.native -use-ocamlfind -package io-system
    ./main.native
