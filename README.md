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


## Documentation
See the complete documentation online on [doc/io-effects-unix](http://clarus.github.io/doc/io-effects-unix/IoEffectsUnix.Unix.html).
