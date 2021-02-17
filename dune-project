(lang dune 1.11)

(generate_opam_files true)

(name refl)
(license "BSD-2-Clause")
(maintainers "Thierry Martinez <thierry.martinez@inria.fr>")
(authors "Thierry Martinez <thierry.martinez@inria.fr>")
(source (uri "git+https://github.com/thierry-martinez/refl"))
(homepage "https://github.com/thierry-martinez/refl")
(bug_reports "https://github.com/thierry-martinez/refl")
(documentation "https://github.com/thierry-martinez/refl")
(version "0.4.0")

(package
 (name refl)
 (synopsis "PPX deriver for reflection")
 (description "\
PPX deriver for reflection
")
 (depends
  (ocaml (>= 4.08.0))
  (dune (>= 1.11.0))
  (stdcompat (>= 14))
  (fix (>= 20200131))
  (metapp (>= 0.4.0))
  (metaquot (>= 0.4.0))
  (traverse (>= 0.3.0))
  (odoc (and :with-doc (>= 1.5.1)))))