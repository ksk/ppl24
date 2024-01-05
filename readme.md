# Programs for PPL 2024 submission

Here are files for the paper 
 "いくつかの組合せ子の非停止性について"
submitted to PPL 2024.

* [Directory `ocaml/`](#directory-ocaml)
* [Directory `coq/`](#directory-coq)


## Directory `ocaml/`
 It contains the OCaml program which tries to find
 a tree automaton disproving termination.
 The program requires the OCaml compiler (>= 4.14) 
 and Microsoft's Z3 SMT solver (>= 4.12).
 Running `make` at the directory will build an executable program `ppl24`.

### How to use `ppl24`
The command `ppl24` is always run with two arguments, 
the first is the name of the combinator
and 
the second is the maximum number of states of disproving tree automata.
To find a (less than or equal to 5-state) tree automaton
disproving the termination of the O combinator,
run
```
$ ppl24 O 5
```
where `$` denotes the command prompt.
The following names of combinators are supported:
- `O` : O x y -> y (x y)
- `S` : S x y z -> x z (y z)
- `P` : P x y z -> z (x y z)
- `P3` : P3 x y z -> y (x z y)
- `Phi` : Phi x y z w -> x (y w) (z w)
- `Phi2` : Phi2 x y z w1 w2 -> x (y w1 w2) (z w1 w2)
- `S1` : S1 x y z w -> x y w (z w)
- `S2` : S2 x y z w -> x z w (y z w)
- `S3` : S3 x y z w v -> x y (z v) (w v)
- `S4` : S4 x y z w v -> z (x w v) (y w v)
- `D1` : D1 x y z w -> x z (y w) (x z)
- `D2` : D2 x y z w -> x w (y z) (x w)

## Directory `coq/`
 It contains the Coq proof script `Theta.v` which disproves 
 the termination of O-like combinaors.
 The script requires the Coq proof assistant (>= 8.18) with zify.





