Set Nested Proofs Allowed.
(** *The formats here are derived using automation.
    We can still add them to automation using the appropriate hooks.
 *)

Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.Base.UnionFormat
        Fiat.Common.SumType
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.Sequence.
Require Import
        Fiat.Common.List.ListFacts
        Fiat.Common.ilist.
Require Import
        Coq.Strings.String
        Coq.Sorting.Permutation
        Coq.Arith.Factorial
        Coq.Arith.Compare_dec.
Require Import Coq.Logic.Eqdep_dec.
Require Import Bedrock.Word.

(*Aligned*)
Require Import
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedSumType
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecodeMonad.

(* Automation *)
Require Import
        Fiat.Narcissus.Automation.NormalizeFormats
        Fiat.Narcissus.Automation.ExtractData
        Fiat.Narcissus.Automation.Common
        Fiat.Narcissus.Automation.Invertible.

Require Import Fiat.Narcissus.BinLib.

(*Fin.t*)
Require Import
        Coq.Logic.FinFun.
Import Fin2Restrict.


Require Import 
        Coq.ZArith.ZArith.


(** Some useful exploratory tactics *)
        
        Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
        Proof. auto. Qed.
        Lemma modusponensT: forall (P Q: Type), P -> (P -> Q) -> Q.
Proof. auto. Qed.

        Ltac exploit x :=
          refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _ _) _)
          || refine (modusponens _ _ (x _ _ _) _)
          || refine (modusponens _ _ (x _ _) _)
          || refine (modusponens _ _ (x _) _).
        
        Ltac exploitT x :=
         refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _ _) _)
          || refine (modusponensT _ _ (x _ _ _) _)
          || refine (modusponensT _ _ (x _ _) _)
          || refine (modusponensT _ _ (x _) _).

Ltac ez_apply:=
    match goal with
      [H: _ |- _] => eapply H
    end.






(*+ Fin.t *)
(* Fin.t represent indices to an vector/array, known to be in bound.
   We will use Fin.t as index for the sumtype and primarily use words to encode it *)
Section Fin.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  
  Definition fin2Word {n:nat} (sz:nat) (idx: Fin.t n): word sz :=
    Word.natToWord sz (f2n idx).
  Definition word2Fin {n sz:nat} (w: word sz): Fin.t (S n).
  Proof. apply (@Fin.of_nat_lt (min (wordToNat w) n) (S n)).
         lia.
  Defined.

  (** *The Format*)
  Definition Format_Fin {n:nat} (sz:nat): FormatM (Fin.t n) ByteString:=
    format_word ◦ (@fin2Word n sz). 

  (** *The encoder*)
  Definition Fin_AlignEncoder {n} sz:=
    (Projection_AlignedEncodeM (fun n0 : nat => SetCurrentBytes)
                               (@fin2Word n (sz * 8))).

  Lemma Fin_Encoder_Correct:
    forall (n sz:nat),
      (* These two hypothesis are adopted from format_word*)
      (forall (ce : CacheFormat) (n0 m : nat),
          addE (addE ce n0) m = addE ce (n0 + m)) ->
      (forall ce : CacheFormat, addE ce 0 = ce) ->
      CorrectAlignedEncoder (@Format_Fin n (sz * 8)) (Fin_AlignEncoder sz).
  Proof.
    intros.
    eapply CorrectAlignedEncoderProjection, CorrectAlignedEncoderForFormatNChar.
    1,2: assumption.
  Qed.
  
  (** *The Decoder*)

  Let Fin_invariant {n} sz (fi:Fin.t n):= (f2n fi < pow2 sz)%nat.

  
  Instance CInv_finToWord' (n sz:nat):
    ConditionallyInvertible (@fin2Word (S n) sz) (fun a => (S n) < pow2 sz)%nat (@word2Fin n sz).
  Proof. constructor; intros.
         unfold word2Fin, fin2Word.
         match goal with
           |- @Fin2Restrict.n2f ?a ?b ?c = _ =>
             (*forget c: TODO: make tactic*)
             remember c as X eqn:HH; clear HH
         end.
         revert X; rewrite wordToNat_natToWord_idempotent.
         - intros.
           apply Fin2Restrict.f2n_inj.
           rewrite Fin2Restrict.f2n_n2f.
           rewrite min_l; auto.
           pose proof (Fin2Restrict.f2n_ok a). lia.
         - eapply Nomega.Nlt_in.
           rewrite Npow2_nat,Nnat.Nat2N.id.
           etransitivity. eapply Fin2Restrict.f2n_ok.
           assumption.
  Qed.

  Definition Fin_Decoder n sz :=
    sequence_Decode decode_word
                    (fun (v1 : word sz) t' cach =>
                       if 
                         ((lt_dec (f2n (@word2Fin n sz v1)) (pow2 sz)) &&
                            weqb (fin2Word sz (@word2Fin n sz v1)) v1)%bool
                       then Some (@word2Fin n sz v1, t', cach)
                       else None).
  
  Lemma Fin_Decoder_Correct n sz cache_inv
        (P_OK:  cache_inv_Property cache_inv
                                   (fun P : CacheDecode -> Prop =>
                                      forall (b : nat) (cd : CacheDecode), P cd -> P (addD cd b))):
    (S n < pow2 sz)%nat ->
    (CorrectDecoder AlignedByteString.ByteStringQueueMonoid
                    (Fin_invariant sz) (Fin_invariant sz) eq 
                    (@Format_Fin (S n) sz)
                    (Fin_Decoder n sz) cache_inv (@Format_Fin (S n) sz)).
  Proof.
    unfold Fin_invariant.
    normalize_format. 
    eapply format_sequence_correct.
    + do 2 instantiate(1:=constant True). simpl.
      unfold cache_inv_Property. auto.
    + intros.
      eapply Word_decode_correct; auto.
    + simpl; auto.
    + extract_view.
  Qed.

  (** *Aligned decoder*)
  (* We provide two cases:
     1. Index encoded in one Byte
     2. Index encoded in multiple Bytes
   *) 
  Definition IndexAligneDecoderByte (n numBytes : nat):
    AlignedDecodeM (Fin.t (S n)) numBytes:=
    BindAlignedDecodeM
      GetCurrentByte
      (fun b  =>
         (fun (b0 : word 8) =>
            if
              (lt_dec (@f2n (S n) (word2Fin b0)) (pow2 8) &&
                 weqb (@fin2Word (S n) 8 (word2Fin b0)) b0)%bool
            then (fun numBytes0 : nat => ReturnAlignedDecodeM (word2Fin b0))  numBytes
            else ThrowAlignedDecodeM) b).

  Definition IndexAligneDecoder_return (n sz numBytes : nat) (w: word sz):
    AlignedDecodeM (Fin.t (S n)) numBytes:=
    if
      (lt_dec (@f2n (S n) (word2Fin w)) (pow2 sz) &&
         weqb (@fin2Word (S n) sz (word2Fin w)) w)%bool
    then (fun _ => ReturnAlignedDecodeM (word2Fin w))  numBytes
    else ThrowAlignedDecodeM.
  
  Definition IndexAligneDecoder (n szB numBytes : nat):
    AlignedDecodeM (Fin.t (S n)) numBytes:=
    let sz := szB * 8 in
    BindAlignedDecodeM
      (GetCurrentBytes szB)
      (IndexAligneDecoder_return n (szB*8) numBytes).

  Lemma AlignedDecodeFinByte n:
    DecodeMEquivAlignedDecodeM
      (Fin_Decoder n 8) (IndexAligneDecoderByte n).
  Proof.
    unfold Fin_Decoder, sequence_Decode.
    eapply @AlignedDecodeBindCharM; intros; eauto.
    eapply @AlignedDecode_ifb.
    eapply @Return_DecodeMEquivAlignedDecodeM.
  Defined.

  Lemma AlignedDecodeFin (n szB: nat):
    (forall (cd : CacheDecode) (n0 m : nat),
        addD (addD cd n0) m = addD cd (n0 + m)) ->
    (forall cd : CacheDecode, addD cd 0 = cd) -> 
    DecodeMEquivAlignedDecodeM
      (Fin_Decoder n (szB * 8)) (@IndexAligneDecoder n szB).
  Proof.
    intros; unfold Fin_Decoder, sequence_Decode,IndexAligneDecoder.
    eapply Bind_DecodeMEquivAlignedDecodeM.
    - eapply AlignedDecodeNCharM; assumption.
    - intros.
      eapply @AlignedDecode_ifb.
      eapply @Return_DecodeMEquivAlignedDecodeM.
  Defined.
  
  Lemma AlignedDecodeFinByte_Bind {C: Type} (n: nat):
    forall (t: Fin.t (S n) -> DecodeM (C * ByteString) ByteString)
      (t': Fin.t (S n) -> forall numBytes : nat, AlignedDecodeM C numBytes),
      (forall a, DecodeMEquivAlignedDecodeM (t a) (t' a))-> 
      DecodeMEquivAlignedDecodeM
        (fun b cd =>
           `(a, b0, env) <- Fin_Decoder n 8 b cd;
         t a b0 env)
        (fun numBytes =>
           BindAlignedDecodeM
             (IndexAligneDecoderByte n numBytes)
             (fun a => t' a numBytes)).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply AlignedDecodeFinByte.
  Defined.
  
  Lemma AlignedDecodeFin_Bind {C: Type}:
    (forall (cd : CacheDecode) (n0 m : nat),
        addD (addD cd n0) m = addD cd (n0 + m)) ->
    (forall cd : CacheDecode, addD cd 0 = cd) -> 
    forall n szB (t: Fin.t (S n) -> DecodeM (C * ByteString) ByteString)
      (t': Fin.t (S n) -> forall numBytes : nat, AlignedDecodeM C numBytes),
      (forall a, DecodeMEquivAlignedDecodeM (t a) (t' a))-> 
      DecodeMEquivAlignedDecodeM
        (fun b cd =>
           `(a, b0, env) <- Fin_Decoder n (szB * 8) b cd;
         t a b0 env)
        (fun numBytes =>
           BindAlignedDecodeM
             (IndexAligneDecoder n szB numBytes)
             (fun a => t' a numBytes)).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply AlignedDecodeFin; assumption.
  Defined.

End Fin.


(*The following two tactics help in automation, solving the side
conditions of synthetizing the encoder*)
Ltac build_evar_ilist:=
  (* NOTE: this function usees SHELVE for subgoals
             you might want to use ilist_of_evar is better instead
   *)
  match goal with
    |- ilist (Vector.nil _) => constructor
  | |- ilist _ => econstructor; [shelve|build_evar_ilist]
  | |- ?x => idtac x; fail "Not an ilist"
  end.
Ltac split_evar_ilist E:=
  (* I don't know how to instantiate an evar by name, so I use this hack
     with `replace` I create a new goal where the varaible is at location 1
     then I can instantiate by name.

     Fails if the type of the evar has uninstantiated variables too. 
   *)
  match type of E with
    ?T => makeEvar T ltac:(fun x => replace E with x);
         [|unshelve instantiate(1:=_);
           [build_evar_ilist| reflexivity]]
  end.
Ltac split_iterate:=
  lazymatch goal with
    |- IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
        (fun idx => CorrectAlignedEncoder (ith ?formats idx) (ith ?ils idx)) =>
      (* break the evar ilist in the hole above*)
      (* NOTE: this uses shelve and unshelve which are not allways great for automation.
                          there is probab    ly a better solution using `ilist_of_evar`
                          (see how it's used    in `apply_combinator_rule'`)
       *)
      split_evar_ilist ils;
      (*Then split the Iterate goal into multiple goals *) 
      repeat apply Build_prim_prod; simpl; try exact tt; try exact I
  end.



(*+ Vector util *)
(* We provide aditional functionality for working with vectors.
   Santiago: I'm surprised none of these is in the standard library or Fiat. Did I miss them? *)
Section Vector.
  Context {T: Type}.
  Context (code_dec: forall (x y: T), {x = y} + {x <> y}). (* Decidable equality*)

  Lemma Vector_In_nth:
    forall n (v: Vector.t T n) a,
      Vector.In a v ->
      exists fn, Vector.nth v fn = a.
  Proof.
    intros.
    dependent induction H.
    - exists Fin.F1; reflexivity.
    - destruct IHIn.
      exists (Fin.FS x0).
      rewrite <- H0. reflexivity.
  Qed.


  Lemma Vector_nth_In:
    forall n fn (v: Vector.t T n),
      Vector.In (Vector.nth v fn) v.
  Proof.
    intros n fn; dependent induction fn.
    - intros; simpl.
      dependent induction v; simpl.
      unfold Vector.nth; simpl.
      constructor.
    - intros v.
      dependent induction v; simpl.
      clear IHv.
      econstructor.
      eapply IHfn.
  Qed.

  (* | Computational version of Vector.In *)
  Fixpoint vin {n} (a: T) (v: Vector.t T n) : bool :=
    match v with
    | Vector.nil => false
    | Vector.cons x aa v' => 
        code_dec a x || vin a v'
    end.
  Lemma vin_Correct:
    forall n (v:Vector.t T n)  x, (Vector.In x v <-> vin x v = true).
  Proof.
    split.
    - intros HH; induction HH.
      + simpl. destruct code_dec; auto.
      + simpl. destruct (code_dec x x0); eauto.
    - induction v.
      + simpl; congruence.
      + simpl. destruct (code_dec x h); subst.
        * constructor.
        * constructor 2; eauto.
  Qed.

  (* | Looks for element v in the vector and returns it's index if found *)
  Fixpoint vindex {n} (a: T) (v: Vector.t T n): option (Fin.t n):=
    match v as t in Vector.t _ n0 return option (Fin.t n0) with
    | Vector.nil => None
    | Vector.cons x aa v' =>
        if code_dec a x then Some (Fin.F1) else
          match vindex a v' with
            None => None
          | Some fn => Some (Fin.FS fn)
          end
    end.

  (* | Finds element in list. It's only correct if the element is in the list. 

     NOTICE that if the element is not in the list, it will return the index
     (S |ls|) which is outside of the list.
   *)
  Fixpoint lindex_total (ls: list T) (a: T) : nat:=
    match ls with
      [] => 0 (* Bogus, element not found*)
    | x::ls' => if code_dec a x then 0 else 1 + (lindex_total ls' a )
    end.

  (*  Total version of `vindex` which returns bogus values when the element is not on the list.
     Otherwise, allways return, only correct when the value is in the list
   *)
  Definition vindex_total {n} (v: Vector.t T (S n)) (a: T) : Fin.t (S n):=
    let s := lt_dec (lindex_total (Vector.to_list v) a) (S n) in
    match s with
    | left l => n2f l
    | in_right => (* impossible case, index is larger than list. Give bogus result.*)
        Fin.F1
    end.
  
  (*Same as `vindex_total` but defined without lists. *)
  Definition vindex_total' {n} (v: Vector.t T (S n)) (a: T) : Fin.t (S n).
    induction n.
    - inversion v; subst.
      exact Fin.F1. (* ^ If they are not equal, returns a bogus value. *)
    - inversion v; subst.
      destruct (code_dec a h).
      + subst.
        exact Fin.F1.
      + eapply Fin.FS.
        eapply (IHn X).
  Defined.


  (* vindex_total is the inverse of Vector.nth *)
  Lemma fint1: forall (a: Fin.t 1), a = Fin.F1.
  Proof.
    intros a. clear. dependent induction a; auto.
    inversion a.
  Qed.
  Lemma fint1': forall (a b: Fin.t 1), a = b.
  Proof.
    intros. etransitivity; [| symmetry];
              eapply fint1.
  Qed.

  (** *Prove the invertibility of Vector.nth (by  vindex_total) *)
  (* We first need several lemmas about vectors, lists and their relation.*)

  Lemma to_list_length: forall n (v: Vector.t T n),
      (| Vector.to_list v |) = n.
  Proof.
    intros; induction v; auto.
    simpl. f_equal.
    eapply IHv.
  Qed.
  Lemma lindex_total_bound:
    forall x (l: list T),
      In x l ->
      (lindex_total l x < (List.length l))%nat.
  Proof.
    intros x ls.
    induction ls.
    - intros ?; exfalso; assumption.
    - simpl; intros.
      destruct (code_dec x a).
      + subst. lia.
      + simpl.
        destruct H.
        * exfalso; auto.
        * eapply IHls in H. lia.
  Qed.

  Lemma f2n_FS: forall n (a: Fin.t n),
      S (f2n a) = f2n (Fin.FS a).
  Proof.
    intros.
    remember (let (i, P) := Fin.to_nat a in
              exist (fun i0 : nat => (i0 < S n)%nat) (S i) (lt_n_S i n P)) as XX.
    unfold f2n.
    match goal with
    | |- ?lhs = proj1_sig ?rhs =>
        replace rhs with XX; subst XX
    end.
    remember (Fin.to_nat a) as A.
    destruct A; reflexivity.
    reflexivity.
  Qed.
  Lemma vector_to_list_nth:
    forall n (v: Vector.t T n) a (def:T),
      Vector.nth v a = List.nth (f2n a) (Vector.to_list v) def.
  Proof.
    intros n. induction n.
    - intros. inversion a.
    - intros.
      dependent induction v; subst; try solve[intros; inversion a].
      clear IHv.
      dependent induction a; try clear IHa.
      + reflexivity.
      + replace (Vector.nth (Vector.cons T h n v) (Fin.FS a)) with
          (Vector.nth v a) by reflexivity.
        erewrite (IHn v a).
        replace (f2n (Fin.FS a)) with (S (f2n a)).
        reflexivity.

        clear.
        eapply f2n_FS.
  Qed.

  Lemma lindex_total_nth:
    forall ls m def, NoDup ls ->
                (m < (| ls |))%nat ->  
                lindex_total ls (nth m ls def) = m.
  Proof.
    clear.
    induction ls. 
    - simpl. intros; lia.
    - intros.
      destruct m; simpl.
      + destruct (code_dec a a); auto. exfalso; auto. 
      + assert (NoDup (a::ls)) by auto. 
        assert (HH:( m < (| ls |))%nat) by (simpl in *; lia).
        destruct (code_dec (nth m ls def) a); cycle 1.
        * simpl in *. rewrite IHls; auto.
          inversion H1; assumption.
        * inversion H1; subst.
          contradict H4.
          eapply nth_In. auto.
  Qed.

  Definition Vector_NoDup {n} (v: Vector.t T (S n)):=
    NoDup (Vector.to_list v).

  Instance CInv_Vectornth {n:nat} (codes: Vector.t T (S n)):
    ConditionallyInvertible (Vector.nth codes) (constant (Vector_NoDup codes)) (vindex_total codes).
  Proof. constructor.
         unfold vindex_total.
         pose proof (to_list_length _ codes); intros.
         remember (Vector.to_list codes) as ls.
         remember (Vector.nth codes a) as x.
         match goal with
         | |- (match ?x with left _ => _ | _ => _ end) = _ => destruct x 
         end.
         - eapply f2n_inj; rewrite f2n_n2f.
           erewrite (vector_to_list_nth _ _ _ x) in Heqx.
           rewrite Heqx.
           remember (f2n a) as m.
           rewrite <- Heqls.
           eapply lindex_total_nth.
           { subst ls. eauto. }
           subst.
           rewrite H.
           eapply f2n_ok.

         - (* simple case, where the index has to be the last element.
            NO! this case should be impossible, the index is at least the length of the list.
            *)
           unshelve erewrite vector_to_list_nth in Heqx; try eassumption.
           contradiction n0.
           rewrite <- H.
           eapply (lindex_total_bound x ls).
           rewrite Heqx, <- Heqls. eapply nth_In.
           rewrite H.
           apply f2n_ok.
  Qed.
  (* also invertible in the other sense*)
  Lemma CInv_vindex_total {n:nat} (codes: Vector.t T (S n)) (HNoDup: Vector_NoDup codes):
    ConditionallyInvertible (vindex_total codes) (fun x => Vector.In x codes) (Vector.nth codes) .
  Proof.
    econstructor; intros.
    eapply Vector_In_nth in H as [? H].
    rewrite <- H.
    edestruct @CInv_Vectornth.
    rewrite CInvRoundTrip; auto.
  Qed.

End Vector.


(*+ Vector index *)
(* Another way to encode Fin.t, is to use a vector of "codes". The
index is determined by the position of the code on the vector.

 We implement a generic version (abstracting the
 type/format/encoder/decoder of the "code") and then instantiate it
 with Words. A future implementation, for XML, would include tags in String.
 *)
Section VectorIndex.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  (*Codes are a decidable type*)
  Context {codeT: Type}. (* The type of the code *)
  Context (code_dec: forall (x y: codeT), {x = y} + {x <> y}). (* Decidable equality*)
  
  (* Format, Encoder, Decoder *)
  Context {codeFormat : FormatM codeT  ByteString}.
  Context (codeEncoder : forall sz : nat, @AlignedEncodeM cache codeT sz).
  Context (codeInv: codeT -> Prop)
          (codeDecode: DecodeM (codeT * ByteString) ByteString).

  (** *The Format*)
  Definition Format_VectorIndex {n} (codes: Vector.t codeT n) : FormatM (Fin.t n) ByteString:=
    codeFormat ◦ Vector.nth codes.

  
  (** *The encoder*)
  Definition VectroIndex_AlignEncoder {n} (codes: Vector.t codeT n):= Projection_AlignedEncodeM codeEncoder (Vector.nth codes).

  Lemma VectorIndex_Encoder_Correct:
    forall {n} (codes: Vector.t codeT n),
      CorrectAlignedEncoder codeFormat codeEncoder -> 
      CorrectAlignedEncoder (Format_VectorIndex codes) (VectroIndex_AlignEncoder codes).
  Proof.
    unfold Format_VectorIndex.
    intros; eapply CorrectAlignedEncoderProjection;
      eassumption.
  Qed.
  Let blah {T}: T -> Prop := constant True.
  (** *The Decoder*)
  Existing Instance CInv_Vectornth.
  Lemma VectorIndex_Decoder_Correct:
    forall {n} (codes: Vector.t codeT (S n)) cache_inv
      BOGUS,
      Vector_NoDup codes ->
      (cache_inv_Property cache_inv (constant True) ->
       CorrectDecoder ByteStringQueueMonoid codeInv 
                      codeInv eq codeFormat codeDecode cache_inv codeFormat) ->
      let invariant := fun x => codeInv (Vector.nth codes x) in 
      { decoder & prod (CorrectDecoder AlignedByteString.ByteStringQueueMonoid
                                       invariant invariant eq 
                                       (Format_VectorIndex codes)
                                       decoder cache_inv (Format_VectorIndex codes))
                       (BOGUS decoder)}.
  Proof.
    intros * HNoDup HCorrectDec.
    do 2 econstructor.
    - unfold Format_VectorIndex.
      normalize_format. 
      eapply format_sequence_correct.
      + do 2 instantiate(1:=constant True). 
        unfold cache_inv_Property. auto.
      + eassumption.
      + intros; apply H. 
      + unshelve instantiate(1:=_).
        intros code.
        intros ??. 
        exact (if vin code_dec code codes then Some (vindex_total code_dec codes code, H, X) else None).
        simpl; intros. eapply CorrectDecoderEmpty.
        * (* build_fully_determined_type *)
          unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw,
            Basics.compose in *; simpl in *.
          let a' := fresh in
          intros a'; try destruct a'; destruct_conjs.
          unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw in *;
            simpl in *; intros. decompose_source_predicate. subst_projections.
          subst_invertible. try rewrite H3. reflexivity.
        * unfold IsProj.
          unfold General.decides.
          destruct (vin code_dec v1 codes) eqn:HH.
          -- eapply vin_Correct in HH.
             simpl.
             match goal with
               |- context [codeInv ?x] =>
                 assert (HH0:x = v1);
                 [| rewrite HH0]
             end; try split; eauto.
             apply CInv_vindex_total; auto.
          -- intros [_ Hfalse].
  Abort. (* We can achieve the same goal with Enum, already proved.
            For now this is not needed. 
          *)
  
End VectorIndex.



(*+ Modular Indexed SumTypes *)
  (* | The IndexedSumType is modular over any other format/encoder/decoder for Fin.t *)
  
  (* This lemma is dumplicated from AlignedAutomation.v to avoid circular references.
     TODO: Refactor to reduce duplicagtion. 
   *)
Section IndexedSumType_Modular.

  Lemma encoder_empty_cache_OK {S1 S2}
        (format_A : FormatM S1 ByteString)
        (format_B : FormatM S2 ByteString)
        (encode_B : forall sz, AlignedEncodeM sz)
        (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
    : forall (s1 : S1) (s2 : S2) (env : CacheFormat) (tenv' tenv'' : ByteString * CacheFormat),
      format_B s2 env ∋ tenv' ->
      format_A s1 (snd tenv') ∋ tenv'' ->
      exists tenv3 tenv4 : _ * CacheFormat,
        projT1 encoder_B_OK s2 env = Some tenv3
        /\ format_A s1 (snd tenv3) ∋ tenv4.
  Proof.
    intros.
    destruct tenv'; destruct tenv''; simpl in *.
    match goal with
      |- exists _ _, ?b = _ /\ _ =>  destruct b as [ [? ?] | ] eqn: ?
    end.
    - eexists _, _; simpl in *; split; intros; eauto.
      simpl in *.
      destruct c; destruct c1; eauto.
    - eapply (proj1 (projT2 encoder_B_OK)) in Heqo.
      eapply Heqo in H; intuition.
  Qed.

  
  (** *The Format*)
  Definition format_IndexedSumType_total {m} (sz: nat)
             (types : Vector.t Type m)
             (formats : ilist (B := fun T => FormatM T ByteString) types)
    : FormatM (SumType types) ByteString
    := format_word ◦ fin2Word sz ∘ SumType_index types ++
                   format_SumType types formats.

  (*We will abstract the format for Fin.t to make proofs modular and simpler. *)
  Definition format_IndexedSumType {m} (sz: nat)
             (types : Vector.t Type m)
             (formats : ilist (B := fun T => FormatM T ByteString) types)
             (format_Fin : FormatM (Fin.t m) ByteString)
    : FormatM (SumType types) ByteString
    := format_Fin ◦ SumType_index types ++
                  format_SumType types formats.

  (** *The encoder*)
  Definition IndexedSumType_AlignEncoder:= False.

  Definition encoder_IndexedSumType {n} 
             (encode_fin: forall sz0 : nat,
                 @AlignedEncodeM EmptyStore.test_cache (Fin.t n) sz0)
             {types}
             (encoders: ilist (B:= fun T : Type =>
                                     forall sz : nat, @AlignedEncodeM _ T sz) types)
             (sz : nat)
    : @AlignedEncodeM _ (@SumType n types) sz
    :=
    (Projection_AlignedEncodeM encode_fin
                               (SumType_index types) sz>>
                               AlignedEncodeSumType encoders sz)%AlignedEncodeM.
  
  Lemma IndexedSumType_Encoder_Correct:
    forall (n sz:nat)
           types
           formats
           (encoders: ilist (B:= fun T : Type =>
                                   forall sz : nat, @AlignedEncodeM _ T sz) types)
           (Encoders_OK:   IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                             (fun idx : Fin.t n =>
                                CorrectAlignedEncoder (ith (B:=fun T : Type =>
                                                                 FormatM T ByteString)
                                                           formats idx)
                                                      (ith encoders idx)))
           format_fin
           (encode_fin: forall sz0 : nat,
               @AlignedEncodeM EmptyStore.test_cache (Fin.t n) sz0)
           (EncodeFin_OK: CorrectAlignedEncoder format_fin encode_fin), 
      CorrectAlignedEncoder (@format_IndexedSumType n sz types formats format_fin)
                            (encoder_IndexedSumType encode_fin encoders).
  Proof.
    intros; unfold format_IndexedSumType.
    eapply @CorrectAlignedEncoderForThenC; cycle 1.
    - (* The sumtype case *)
      (*The following code mimics what the automation does when
        it applies `@CorrectAlignedEncoderForThenC` *)
      unshelve (instantiate(1:= _)).
      2: eauto using encoder_empty_cache_OK.
      (*The Fin.t case *)

      eapply CorrectAlignedEncoderProjection.
      eassumption.
      
    - (* Correct sumtype.*)
      eapply CorrectAlignedEncoderForFormatSumType.
      eapply Encoders_OK.
  Qed.
  
  (** *The Decoder*)
  Definition decoder_IndexedSumType 
             {n types}
             (decoder_fin: DecodeM (Fin.t n * ByteString) ByteString)
             (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types)
    := sequence_Decode decoder_fin
                       (decode_SumType types decoders).

  Lemma IndexedSumType_Decoder_Correct (n sz: nat)
        types
        formats
        cache_inv
        format_fin
        view_fin
        P_inv1
        (invariants: ilist (B:= fun T => T -> Prop) types)
        (cache_invariants: Vector.t (Ensembles.Ensemble (CacheDecode -> Prop)) n)
        (cache_invariants_OK: cache_inv_Property cache_inv (fun P =>
                                                              P_inv1 P /\
                                                                IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                                                                  (fun idx : Fin.t n => Vector.nth cache_invariants idx P)))
        (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types)
        (decoders_OK: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                        (fun idx : Fin.t n =>
                           cache_inv_Property cache_inv (Vector.nth cache_invariants idx) ->
                           CorrectDecoder BinLib.ByteStringQueueMonoid 
                                          (ith invariants idx) (ith invariants idx) eq 
                                          (ith formats idx) (ith decoders idx) cache_inv 
                                          (ith formats idx)))
        (decoder_fin: DecodeM (Fin.t n * ByteString) ByteString)
        (fin_decoder_OK: (*I think we don't need it*)
          cache_inv_Property cache_inv P_inv1 -> 
          CorrectDecoder BinLib.ByteStringQueueMonoid view_fin
                         view_fin eq format_fin decoder_fin cache_inv format_fin)
    :
    let source_pred st :=
      view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st) in
    CorrectDecoder ByteStringQueueMonoid
                   source_pred source_pred
                   eq 
                   (@format_IndexedSumType n sz types formats format_fin)
                   (decoder_IndexedSumType decoder_fin decoders)
                   cache_inv
                   (@format_IndexedSumType n sz types formats format_fin)
  .
  Proof.
    unfold format_IndexedSumType.
    eapply format_sequence_correct; cycle 1.
    + (*Format Fin *)
      unshelve eapply fin_decoder_OK.
    + intros? HH; apply HH. 
    + intros.
      unfold IsProj.
      
      (* Change the source pred:
         1. We need to remove the part that talks about the fin_view and
            Here we use the hypothesis the assumes `fin_view`
         2. Write it in the form expected by `SumType_decode_correct`
       *)
      eapply weaken_view_predicate_Proper.
      unfold pointwise_relation, impl; simpl.
      instantiate(1:= fun a => SumType_index types a = v1 /\ ith invariants (SumType_index types a) (SumType_proj types a)).
      simpl. intros ? [].
      repeat (split; eauto).
      rewrite H1; eauto.

      
      (* Change the view pred:
         Same as above, but eaasier because it's in the other direction.
       *)
      eapply weaken_source_pred_Proper.
      instantiate(1:= fun a => SumType_index types a = v1 /\ ith invariants (SumType_index types a) (SumType_proj types a)).
      unfold pointwise_relation, flip, impl; simpl.
      intuition.
      
      (* Now we should be able to apply the lemma*)
      eapply SumType_decode_correct.
      
      * unshelve (instantiate(1:=cache_invariants)).
        eapply decoders_OK.
      * eapply H.
    + (*The first one is for Fin.t,
        We think is not needed
       *)
      clear - cache_invariants_OK.
      eapply cache_invariants_OK.
  Qed.
  
  
End IndexedSumType_Modular.



(*+ Indexed SumTypes with Words *)
(* Specialized to using words directly to encode the Fin.t index. *)
Section IndexedSumTypeWord.
  (* In this section, we specialize the fromat/encoder/decoder to use a word as index. *)

  (** *The Format*)
  (*We will abstract the format for Fin.t to make proofs modular and simpler. *)
  Definition format_IndexedSumType_word {m} (sz: nat)
             {types : Vector.t Type m}
             (formats : ilist (B := fun T => FormatM T ByteString) types)
    : FormatM (SumType types) ByteString
    := format_IndexedSumType sz types formats (@Format_Fin _ _ m sz).

  (** *The encoder*)
  
  Lemma IndexedSumType_Encoder_Correct':
    forall (n sz:nat)
           types
           formats
           (* The following two hyp are inherited from encoding words*)
           (addE_addE_plus : forall (ce : CacheFormat) (n m : nat),
               addE (addE ce n) m = addE ce (n + m))
           (addE_0 : forall ce : CacheFormat, addE ce 0 = ce)
           (encoders: ilist (B:= fun T : Type =>
                                   forall sz : nat, @AlignedEncodeM _ T sz) types)
           (Encoders_OK:   IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                             (fun idx : Fin.t n =>
                                CorrectAlignedEncoder (ith (B:=fun T : Type =>
                                                                 FormatM T ByteString)
                                                           formats idx)
                                                      (ith encoders idx))), 
      CorrectAlignedEncoder (format_IndexedSumType_word (sz * 8) formats)
                            (encoder_IndexedSumType (Fin_AlignEncoder sz) encoders).
  Proof.
    intros.
    apply IndexedSumType_Encoder_Correct; auto.
    apply Fin_Encoder_Correct; auto.
  Qed.
  
  (** *The Decoder*)
  Let decoder_IndexedSumType_full 
      {n} sz {types}
      (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types)
      := @decoder_IndexedSumType (S n) types (Fin_Decoder n sz) decoders.

  Lemma IndexedSumTypeWord_Decoder_Correct (n sz: nat):
    let m:= S n in
    forall types
           formats
           cache_inv
           (* inherited from fin_format*)
           (Bound_OK: (S n < pow2 sz)%nat) 
           (* inherited from formta words*)
           (invariants: ilist (B:= fun T => T -> Prop) types)
           (cache_invariants: Vector.t (Ensembles.Ensemble (CacheDecode -> Prop)) m) 
           (cache_invariants_OK:
             cache_inv_Property cache_inv
                                (fun P : CacheDecode -> Prop =>
                                   (fun P0 : CacheDecode -> Prop =>
                                      forall (b : nat) (cd : CacheDecode), P0 cd -> P0 (addD cd b)) P /\
                                     IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                                       (fun idx : Fin.t (S n) => Vector.nth cache_invariants idx P)))
           (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types)
           (decoders_OK: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                           (fun idx : Fin.t m =>
                              cache_inv_Property cache_inv (Vector.nth cache_invariants idx) ->
                              CorrectDecoder BinLib.ByteStringQueueMonoid 
                                             (ith invariants idx) (ith invariants idx) eq 
                                             (ith formats idx) (ith decoders idx) cache_inv 
                                             (ith formats idx)))
    ,
      let source_pred st :=
        (f2n (SumType_index types st) < pow2 sz)%nat /\ ith invariants (SumType_index types st) (SumType_proj types st) in
      CorrectDecoder ByteStringQueueMonoid
                     source_pred source_pred
                     eq 
                     (format_IndexedSumType_word sz formats)
                     (@decoder_IndexedSumType_full n sz types decoders)
                     cache_inv
                     (format_IndexedSumType_word sz formats)
  .
  Proof.
    intros.
    unfold format_IndexedSumType_word, decoder_IndexedSumType_full.
    subst m.
    eapply (IndexedSumType_Decoder_Correct (S n) sz types formats cache_inv  (Format_Fin sz) (fun st:Fin.t (S n) => (f2n st  < pow2 sz)%nat)); eauto.

    intros; eapply Fin_Decoder_Correct; eauto.
    
  Qed.

  (* An easy way to build ilists invariants with all  `constant True` *)
  Fixpoint ilist_constant_T {n: nat} (types: Vector.t Type n):
    ilist  (B:= fun T => T -> Prop) types:=
    match types as t0 in (Vector.t _ n0) return @ilist _  _ n0 t0 with
      Vector.nil => tt
    | @Vector.cons _ a n0 types0 =>
        {| prim_fst := constant True; prim_snd := (@ilist_constant_T n0 types0) |}
    end.
  
End IndexedSumTypeWord.


(* Creates all the veriables inside ilists and vectors to apply the lemma*)
Ltac apply_IndexedSumType_Decoder_Correct n types :=
        let types' := eval unfold types in types in
          ilist_of_evar (fun T => DecodeM (T * ByteString) ByteString) types'
                        ltac:(fun decoders' =>
                                ilist_of_evar (fun T : Type => T -> Prop) types'
                                              ltac:(fun invariants' =>
                                                      Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                                                                     ltac:(fun cache_invariants' =>
                                                                             eapply IndexedSumType_Decoder_Correct with
                                                                             (cache_invariants := cache_invariants')
                                                                             (invariants := invariants')
                                                                             (decoders := decoders')))).

Ltac apply_IndexedSumTypeWord_Decoder_Correct n types :=
  let types' := eval unfold types in types in 
    ilist_of_evar (fun T => DecodeM (T * ByteString) ByteString) types'
                  ltac:(fun decoders' =>
                          Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                                         ltac:(fun cache_invariants'  =>
                                                 eapply IndexedSumTypeWord_Decoder_Correct with
                                                 (cache_invariants:= cache_invariants')
                                                 (decoders:= decoders'))).

      

Global Opaque format_IndexedSumType.




(*+ Indexed SumTypes with Enums *)
(* Specialized to using words directly to encode the Fin.t index. *)
Section IndexedSumTypeEnum.
  (* In this section, we specialize the fromat/encoder/decoder to use a Enums as index. *)

  Context {sz: nat}. (* Size of words *)
  Context (n:nat) (codes: Vector.t (word sz) (S n)).
  
  (** *The Format*)
  (*We will abstract the format for Fin.t to make proofs modular and simpler. *)
  Definition format_IndexedSumType_enum
             {types : Vector.t Type (S n)}
             (formats : ilist (B := fun T => FormatM T ByteString) types)
    : FormatM (SumType types) ByteString
    := format_IndexedSumType sz types formats (@format_enum n _ _ _ _ _ sz codes).
  
(*   (** *The encoder*) *)
(*   Lemma IndexedSumType_enum_Encoder_Correct': *)
(*     forall (n sz:nat) *)
(*            types *)
(*            formats *)
(*            (* The following two hyp are inherited from encoding words*) *)
(*            (addE_addE_plus : forall (ce : CacheFormat) (n m : nat), *)
(*                addE (addE ce n) m = addE ce (n + m)) *)
(*            (addE_0 : forall ce : CacheFormat, addE ce 0 = ce) *)
(*            (encoders: ilist (B:= fun T : Type => *)
(*                                    forall sz : nat, @AlignedEncodeM _ T sz) types) *)
(*            (Encoders_OK:   IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex *)
(*                              (fun idx : Fin.t n => *)
(*                                 CorrectAlignedEncoder (ith (B:=fun T : Type => *)
(*                                                                  FormatM T ByteString) *)
(*                                                            formats idx) *)
(*                                                       (ith encoders idx))),  *)
(*       CorrectAlignedEncoder (format_IndexedSumType_word (sz * 8) formats) *)
(*                             (encoder_IndexedSumType (Fin_AlignEncoder sz) encoders). *)
(*   Proof. *)
(*     intros. *)
(*     apply IndexedSumType_Encoder_Correct; auto. *)
(*     apply Fin_Encoder_Correct; auto. *)
(*   Qed. *)
  
(*   (** *The Decoder*) *)
(*   Let decoder_IndexedSumType_full  *)
(*       {n} sz {types} *)
(*       (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types) *)
(*       := @decoder_IndexedSumType (S n) types (Fin_Decoder n sz) decoders. *)

(*   Lemma IndexedSumTypeWord_Decoder_Correct (n sz: nat): *)
(*     let m:= S n in *)
(*     forall types *)
(*            formats *)
(*            cache_inv *)
(*            (* inherited from fin_format*) *)
(*            (Bound_OK: (S n < pow2 sz)%nat)  *)
(*            (* inherited from formta words*) *)
(*            (invariants: ilist (B:= fun T => T -> Prop) types) *)
(*            (cache_invariants: Vector.t (Ensembles.Ensemble (CacheDecode -> Prop)) m)  *)
(*            (cache_invariants_OK: *)
(*              cache_inv_Property cache_inv *)
(*                                 (fun P : CacheDecode -> Prop => *)
(*                                    (fun P0 : CacheDecode -> Prop => *)
(*                                       forall (b : nat) (cd : CacheDecode), P0 cd -> P0 (addD cd b)) P /\ *)
(*                                      IterateBoundedIndex.Iterate_Ensemble_BoundedIndex *)
(*                                        (fun idx : Fin.t (S n) => Vector.nth cache_invariants idx P))) *)
(*            (decoders: ilist (B:= fun T => DecodeM (T * ByteString) ByteString) types) *)
(*            (decoders_OK: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex *)
(*                            (fun idx : Fin.t m => *)
(*                               cache_inv_Property cache_inv (Vector.nth cache_invariants idx) -> *)
(*                               CorrectDecoder BinLib.ByteStringQueueMonoid  *)
(*                                              (ith invariants idx) (ith invariants idx) eq  *)
(*                                              (ith formats idx) (ith decoders idx) cache_inv  *)
(*                                              (ith formats idx))) *)
(*     , *)
(*       let source_pred st := *)
(*         (f2n (SumType_index types st) < pow2 sz)%nat /\ ith invariants (SumType_index types st) (SumType_proj types st) in *)
(*       CorrectDecoder ByteStringQueueMonoid *)
(*                      source_pred source_pred *)
(*                      eq  *)
(*                      (format_IndexedSumType_word sz formats) *)
(*                      (@decoder_IndexedSumType_full n sz types decoders) *)
(*                      cache_inv *)
(*                      (format_IndexedSumType_word sz formats) *)
(*   . *)
(*   Proof. *)
(*     intros. *)
(*     unfold format_IndexedSumType_word, decoder_IndexedSumType_full. *)
(*     subst m. *)
(*     eapply (IndexedSumType_Decoder_Correct (S n) sz types formats cache_inv  (Format_Fin sz) (fun st:Fin.t (S n) => (f2n st  < pow2 sz)%nat)); eauto. *)

(*     intros; eapply Fin_Decoder_Correct; eauto. *)
    
(*   Qed. *)

(*   (* An easy way to build ilists invariants with all  `constant True` *) *)
(*   Fixpoint ilist_constant_T {n: nat} (types: Vector.t Type n): *)
(*     ilist  (B:= fun T => T -> Prop) types:= *)
(*     match types as t0 in (Vector.t _ n0) return @ilist _  _ n0 t0 with *)
(*       Vector.nil => tt *)
(*     | @Vector.cons _ a n0 types0 => *)
(*         {| prim_fst := constant True; prim_snd := (@ilist_constant_T n0 types0) |} *)
(*     end. *)
  
End IndexedSumTypeEnum.


             
