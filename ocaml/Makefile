default:
	ocamlbuild ioSystem.cma ioSystem.cmxa -use-ocamlfind -package lwt,lwt.unix,num

install: default
	ocamlfind install io-system META _build/ioSystem.cmi _build/ioSystem.cmx _build/ioSystem.a _build/ioSystem.cma _build/ioSystem.cmxa _build/ioSystem.mllib

uninstall:
	ocamlfind remove io-system

clean:
	ocamlbuild -clean
