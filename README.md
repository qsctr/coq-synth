# coq-synth

Synthesizer for Coq terms, intended for use in the [lemmafinder](https://github.com/AishwaryaSivaraman/lemmafinder) tool.

## Install

```shell
opam install . --deps-only
dune build
dune install
```

## Run

The Coq module being loaded should be compiled first.

Terms are printed as they are synthesized. If neither `--num-terms` nor `--max-depth` is specified then the program will run forever.

```shell
$ coq_synth --logical-dir=lia --physical-dir="lemmafinder/benchmark/motivating_example" --module=list_rev --type=lst --params=l1:lst,n:nat --extra-exprs=append,rev --examples='Nil,4=Cons 4 Nil;Cons 1 (Cons 0 Nil),2=Cons 2 (Cons 0 (Cons 1 Nil));Cons 1 (Cons 2 Nil),1=Cons 1 (Cons 2 (Cons 1 Nil))' --num-terms=5
(Cons n (rev l1))
(Cons n (append (rev l1) Nil))
(rev (append (rev (rev l1)) (Cons n Nil)))
(rev (append l1 (Cons n Nil)))
(Cons n (rev (append l1 Nil)))
```

```
OPTIONS
       --debug
           Enable debug output to stderr

       --examples=INPUT1A,INPUT1B,...=OUTPUT1;INPUT2A,INPUT2B,...=OUTPUT2;...
           Input-output examples that the synthesized terms must satisfy

       --extra-exprs=EXPR1,EXPR2,...
           Extra expressions (containing already defined variables) to include
           in the synthesized terms

       --help[=FMT] (default=auto)
           Show this help in format FMT. The value FMT must be one of `auto',
           `pager', `groff' or `plain'. With `auto', the format is `pager` or
           `plain' whenever the TERM env var is `dumb' or undefined.

       --logical-dir=DIRPATH (required)
           The logical directory of the Coq module

       --max-depth=N (absent=infinity)
           The maximum search depth (note: this does not necessarily
           correspond to the depth of terms due to simplification)

       --module=MOD (required)
           The name of the Coq module

       --num-terms=K (absent=infinity)
           The maximum number of terms to return

       --params=PARAM1:TYPE1,PARAM2:TYPE2,...
           The parameters to the synthesized terms

       --physical-dir=DIR (required)
           The physical directory of the Coq module

       --type=TYPE (required)
           The type of the terms to synthesize
```
