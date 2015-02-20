# IO Effects Unix
The Coq effects for Unix.

    Require Import IoEffects.All.
    Require Import IoEffectsUnix.All.
    Require Import ListString.All.

    Import C.Notations.

    Definition hello_world : C.t Unix.effects unit :=
      Unix.log (LString.s "Hello world!").

## Install
Using OPAM for Coq:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install coq:io-effects:unix

## Extraction
To run a program you can extract it to [OCaml](https://ocaml.org/). Install the extraction library:

    opam install coq:io-effects:unix:ocaml

and evaluate:

    Definition main := Extraction.Lwt.run (Extraction.eval hello_world).
    Extraction "main" main.

You can now compile and execute `main.ml`:

    ocamlbuild main.native -use-ocamlfind -package io-effects-unix

## API
See the complete documentation online on [doc/io-effects-unix](http://clarus.github.io/doc/io-effects-unix/IoEffectsUnix.Unix.html).
