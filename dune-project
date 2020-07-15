(lang dune 1.11)

(generate_opam_files true)

(license "BSD-2-Clause")
(maintainers "Thierry Martinez <thierry.martinez@inria.fr>")
(authors "Thierry Martinez <thierry.martinez@inria.fr>")
(source (uri "git+https://github.com/thierry-martinez/refl"))
(homepage "https://github.com/thierry-martinez/refl")
(bug_reports "https://github.com/thierry-martinez/refl")
(documentation "https://github.com/thierry-martinez/refl")
(version "0.1.1")

(package
 (name refl)
 (synopsis "PPX deriver for reflection")
 (description "\
PPX deriver for reflection
")
 (depends
  (ocaml (and (>= 4.03.0) (< 4.12.0)))
  (dune (>= 1.11.0))
  (stdcompat (>= 14))
  (fix (>= 20200131))
  (metapp (>= 0.2.0))
  (metaquot (>= 0.2.0))
  (traverse (>= 0.2.0))))