(lang dune 2.7)

(name coq_synth)

(generate_opam_files true)

(source
 (github qsctr/coq-synth))

(authors "Bretton")

(maintainers "Bretton")

(license MIT)

(package
 (name coq_synth)
 (synopsis "Coq synthesizer")
 (depends
  ocaml
  dune
  base
  cmdliner
  (coq-serapi (= 8.11.0+0.11.0))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
