# OCaml extraction
> Utilities for extraction of system effects to [OCaml](http://ocaml.org/).

This library is automatically included by the main `coq-io-system` package. It is also distributed as an independent opam package which does not depend on Coq. As a result, the compilation of extracted `.ml` files from programs with effects may not depend on Coq.

## Install with opam
Make sure you added the [Coq repository](http://coq.io/opam/):

    opam repo add coq-released https://coq.inria.fr/opam/released

and run:

    opam install coq-io-system-ocaml

## Install from source

    make
    make install
