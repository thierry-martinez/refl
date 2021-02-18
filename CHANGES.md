# v0.4.0 - 2021-02-19
- Port to OCaml 4.12

# v0.3.0 - 2020-09-22
- Port to ppxlib 0.16 / ocaml-migrate-parsetree 2.0.0

- hide refl definitions from ocamldoc by parenthesizing them with documentation
  stoppers (`(**/**)`).

- Fix: support type constructors with shadow type parameters inside type
  declarations where the type parameters are not shadow.

# v0.2.1 - 2020-07-16
- Fix: make lazy values visitable again

# v0.2.0 - 2020-07-15
- Add: Refl.hash provides an hash function for every comparable structure.

- Fix: lazy structure were not annotated with `Lazy kind.

- Fix: Kinds.all did not include `Poly.

# v0.1.0 - 2020-05-11
Initial release
