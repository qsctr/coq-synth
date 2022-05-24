(lang dune 3.0)

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
  (coq-serapi (= 8.13.0+0.13.0))))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
