# coq-synth

Synthesizer for Coq terms, intended for use in the [lemmafinder](https://github.com/AishwaryaSivaraman/lemmafinder) tool.

Only basic data types with no type parameters are supported right now.

## Install

```shell
opam install . --deps-only
dune build
dune install
```

## Run

```shell
$ coq_synth --logical-dir=lia --physical-dir="lemmafinder/benchmark/motivating_example" --module=list_rev --type=lst --max-depth=4 --params=l1:lst,n:nat --extra-vars=append,rev --examples='Nil,4=Cons 4 Nil;Cons 1 (Cons 0 Nil),2=Cons 2 (Cons 0 (Cons 1 Nil));Cons 1 (Cons 2 Nil),1=Cons 1 (Cons 2 (Cons 1 Nil))'
(Cons n (rev l1))
(append Nil (Cons n (rev l1)))
(Cons n (append Nil (rev l1)))
(append (rev Nil) (Cons n (rev l1)))
```

```
OPTIONS
       --debug
           Enable debug output to stderr

       --examples=INPUT1A,INPUT1B,...=OUTPUT1;INPUT2A,INPUT2B,...=OUTPUT2;...
           Input-output examples that the synthesized terms must satisfy

       --extra-vars=VAR1,VAR2,...
           Extra variables (already defined) to include in the synthesized
           terms

       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of `auto',
           `pager', `groff' or `plain'. With `auto', the format is `pager` or
           `plain' whenever the TERM env var is `dumb' or undefined.

       --logical-dir=DIRPATH (required)
           The logical directory of the Coq module

       --max-depth=N (required)
           The maximum depth of terms to synthesize

       --module=MOD (required)
           The name of the Coq module

       --params=PARAM1:TYPE1,PARAM2:TYPE2,...
           The parameters to the synthesized terms

       --physical-dir=DIR (required)
           The physical directory of the Coq module

       --type=TYPE (required)
           The type of the terms to synthesize
```
