# IO Effects for Unix
The Coq effects for Unix.

    Require Import Io.All.
    Require Import IoSystem.All.
    Require Import ListString.All.

    Import C.Notations.

    Definition hello_world : C.t System.effects unit :=
      System.log (LString.s "Hello world!").

## Install
Using OPAM for Coq:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install coq:io:system

## API
See the complete documentation online on [doc/io-system](http://clarus.github.io/doc/io-system/IoSystem.System.html).

## Extraction
To run a program you can extract it to [OCaml](https://ocaml.org/). Do:

    Definition main := Extraction.Lwt.run (Extraction.eval hello_world).
    Extraction "main" main.

You can now compile and execute `main.ml`:

    ocamlbuild main.native -use-ocamlfind -package io-system
    ./main.native
