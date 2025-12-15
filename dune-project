(lang dune 3.17)

(name lfpl)

(generate_opam_files true)

(source
 (github kchokkal3/lfpl-plus))

(authors
 "Ethan Huang <yhuang4@andrew.cmu.edu>"
 "Kandasamy Chokkalingam <kchokkal@andrew.cmu.edu")

(maintainers
 "Ethan Huang <yhuang4@andrew.cmu.edu>"
 "Kandasamy Chokkalingam <kchokkal@andrew.cmu.edu")

(license GPL-3.0-only)

(package
 (name lfpl)
 (synopsis "An implementation of LFPL+")
 (description "An interpreter for extended LFPL")
 (depends ocaml angstrom core core_unix ppx_jane))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
