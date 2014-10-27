(** * Some examples about dealing with finite sets *)
Require Import ADTSynthesis.FiniteSetADTs.

(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

Definition countUniqueSpec (ls : list W) : Comp nat
  := cardinal ls.

Definition countUniqueSpec' (ls : list W) : Comp nat
  := (xs <- to_list (elements ls);
      ret (List.length xs)).

Definition sumUniqueSpec (ls : list W) : Comp W
  := Ensemble_fold_right wplus wzero (elements ls).

Definition unionUniqueSpec1 (ls1 ls2 : list W) : Comp (list W)
  := to_list (elements (ls1 ++ ls2)).
Definition unionUniqueSpec2 (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Union _ (elements ls1) (elements ls2)).

Definition differenceUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls1) (elements ls2)).

Definition symmetricDifferenceUniqueSpec1 (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Union
                _
                (Ensembles.Setminus _ (elements ls1) (elements ls2))
                (Ensembles.Setminus _ (elements ls2) (elements ls1))).

(** Now we refine the implementations. *)
Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec ls).
Proof.
  (** We turn the list into a finite set, and then call 'size' *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition countUniqueImpl' (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec' ls).
Proof.
  (** We turn the list into a finite set, then back into a list, and then call [Datatypes.length]. *)
  (** TODO: Do we care about optimizing this further at this stage? *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

(** And now we do the same for summing. *)

Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (sumUniqueSpec ls).
Proof.
  (** We fold over the list, using a finite set to keep track of what
      we've seen, and every time we see something new, we update our
      running sum.  This should be compiled down to a for loop with an
      in-place update. *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition unionUniqueImpl1 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (unionUniqueSpec1 ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.
