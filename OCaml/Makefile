default:
	ocamlbuild ioEffectsUnix.cma ioEffectsUnix.cmxa -use-ocamlfind -package lwt,lwt.unix

install: default
	ocamlfind install io-effects-unix META _build/ioEffectsUnix.cmi _build/ioEffectsUnix.cmx _build/ioEffectsUnix.a _build/ioEffectsUnix.cma _build/ioEffectsUnix.cmxa _build/ioEffectsUnix.mllib

uninstall:
	ocamlfind remove io-effects-unix

clean:
	ocamlbuild -clean
