# coq-synth

Coq synthesizer

Only basic data types with no type parameters are supported right now.

## Install

```shell
opam install . --deps-only
dune build
dune install
```

## Run

Make a Coq file where the last sentence introduces a goal with the type of the term you want to synthesize, for example
```coq
Definition synth : nat.
```
Then run with the filename, maximum depth of term, and any additional functions or variables to include in the term. All constructors are already included.
```shell
$ coq_synth synth.v 4 Nat.add
0
1
0 + 0
2
0 + 1
1 + 0
S (0 + 0)
3
S (0 + 1)
1 + 1
0 + (0 + 0)
0 + 2
0 + (0 + 1)
1 + (0 + 0)
1 + 2
1 + (0 + 1)
```

```coq
Inductive lst : Type :=
  | Nil : lst
  | Cons : nat -> lst -> lst.

Fixpoint app (l1 : lst) (l2 : lst) : lst :=
  match l1 with
  | Nil => l2
  | Cons n l1' => Cons n (app l1' l2)
  end.

Fixpoint rev (l : lst) : lst :=
  match l with
  | Nil => Nil
  | Cons n l1' => app (rev l1') (Cons n Nil)
  end.

Parameter l1 : lst.
Parameter n : nat.

Definition synth : lst.
```
```shell
$ coq_synth synth.v 3 app rev l1 n
Nil
l1
rev Nil
rev l1
Cons 0 Nil
Cons n Nil
app Nil Nil
app l1 Nil
Cons 0 l1
Cons n l1
app Nil l1
app l1 l1
rev (rev Nil)
rev (rev l1)
Cons 0 (rev Nil)
Cons n (rev Nil)
app Nil (rev Nil)
app l1 (rev Nil)
Cons 0 (rev l1)
Cons n (rev l1)
app Nil (rev l1)
app l1 (rev l1)
```
