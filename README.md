# IO System
> System effects for Coq. See also [Coq.io](http://coq.io/).

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

## API
See the complete documentation online on [v2.3.0](http://coq-io.github.io/doc/system/2.3.0/toc.html).

## Extraction
To run a program you can extract it to [OCaml](https://ocaml.org/). Do:

    Definition main := Extraction.run hello_world.
    Extraction "main" main.

You can now compile and execute `main.ml`:

    ocamlbuild main.native -use-ocamlfind -package io-system
    ./main.native
