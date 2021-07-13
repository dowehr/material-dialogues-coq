# Material Dialogues for First-Order Logic in Constructive Type Theory

Dominik Wehr, Dominik Kirst

## Overview of the Mechanization
All results concerning classical material dialogues are in
[`theories/MaterialDialogues.v`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v).
We give a small overview, connecting the mechanization with the paper.
 - Definition of Classical Material Dialogues: the
   [`Rules`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L5)
   section
 - The congruence machinery for Soundness proofs (Lemma 3): starting with
   [`form_equiv`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L219)
   and culminating in the proof of
   [`equiv_win`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L498)
 - Soundness wrt. a cut-free sequent calculus (Theorem 4):
   [`satisfaction_sound`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L608)
   proves the claim for a fixed model,
   [`mvalid_sound`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L643)
   concludes the result for all models
 - Quasi-Completeness (Lemma 5): In the
   [`QuasiCompleteness`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L651)
   Section. The two sub-results used in the proof of Lemma 5 are proven in
   [`twin_defend`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L731) (Lemma 18)
   and
   [`win_twin`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L782)
   (Lemma 19). Quasi-Completeness is concluded in
   [`mvalid_valid_L`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L829).
 - DeMorgan translation (Lemma 7): The main result (with regards to full
   validity) is in
   [`mvalid_DM`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L1149).
   The lemmas needed to derive this result are spread across the file as
   follows:
   * The weakening principle (Lemma 20) is proven in [`win_weak`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L951)
   * Lemma 21 is proven in [`defense_cut`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L1029)
   * Dialogical cut-elimination (Theorem 21) is proven in [`win_cut`](https://github.com/dowehr/material-dialogues-coq/blob/main/theories/MaterialDialogues.v#L1116)

We have not mechanized Fragment-Completeness (Corollary 6) as a conclusion of
Quasi-Completeness (Lemma 5). This is because doing so would require us to redo
the Quasi-Completeness proof for only the fragment, leading to a lot of
unnecessary code duplication. We have also not mechanized Completeness (Theorem
8) as this would require Fragment-Completeness to be mechanized as well.
As both of these results have, at least on paper, quite trivial proofs, we did not
think mechanizing these results to be worth the additional effort incurred. After all,
the aim of this mechanization is not full coverage of the results but rather to
give confidence in the paper's correctness. This is already accomplished by formalizing
all of the technical results which offer much greater room for error.
 
## How to compile the code

You need to use Coq 8.11.2 and install the [Equations Package](http://mattam82.github.io/Coq-Equations/). This is easiest via [opam](https://opam.ocaml.org):

``` shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq.8.11.2
opam install coq-equations.1.2.1+8.11
```

Afterwards, you can type `make` in the `theories` directory.

## Acknowledgments
All files in the`theories` folder except for `theories/MaterialDialogues.v` were
taken from the mechanization accompanying our article [Completeness Theorems for
First-Order Logic Analysed in Constructive Type Theory - Extended
Version](https://www.ps.uni-saarland.de/extras/fol-completeness-ext/).
