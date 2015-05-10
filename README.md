# IO System

[![Join the chat at https://gitter.im/clarus/io-system](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/clarus/io-system?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
System effects for Coq. See also [coq:io](https://github.com/clarus/io).

    Require Import Io.All.
    Require Import Io.System.All.
    Require Import ListString.All.

    Import C.Notations.

    Definition hello_world (argv : list LString.t) : C.t System.effects unit :=
      System.log (LString.s "Hello world!").

## Install
Using OPAM for Coq:

    opam repo add coq-stable https://github.com/coq/repo-stable.git
    opam install coq:io:system

## API
See the complete documentation online on [doc/io-system](http://clarus.github.io/doc/io-system/Io.System.System.html).

## Extraction
To run a program you can extract it to [OCaml](https://ocaml.org/). Do:

    Definition main := Extraction.run hello_world.
    Extraction "main" main.

You can now compile and execute `main.ml`:

    ocamlbuild main.native -use-ocamlfind -package io-system
    ./main.native
