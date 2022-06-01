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
(* We will use Fin.t as index *)
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
  
End Fin.



(*TThe following two tactics help in automation, solving the side
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


Section IndexedSumType_Modular.

  (* This lemma is dumplicated from AlignedAutomation.v to avoid circular references.
     TODO: Refactor to reduce duplicagtion. 
   *)
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

Section IndexedSumType.


  (** *The Format*)
  (*We will abstract the format for Fin.t to make proofs modular and simpler. *)
  Definition format_IndexedSumType_full {m} (sz: nat)
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
      CorrectAlignedEncoder (format_IndexedSumType_full (sz * 8) formats)
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

  Lemma IndexedSumType_Decoder_Correct' (n sz: nat):
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
                     (format_IndexedSumType_full sz formats)
                     (@decoder_IndexedSumType_full n sz types decoders)
                     cache_inv
                     (format_IndexedSumType_full sz formats)
  .
  Proof.
    intros.
    unfold format_IndexedSumType_full, decoder_IndexedSumType_full.
    subst m.
    eapply (IndexedSumType_Decoder_Correct (S n) sz types formats cache_inv  (Format_Fin sz) (fun st:Fin.t (S n) => (f2n st  < pow2 sz)%nat)); eauto.

    intros; eapply Fin_Decoder_Correct; eauto.
    
  Qed.

End IndexedSumType.




(*Ltacs to apply the lemma*)


(* Use `subst_pow2; lia` instead *)
(* (* Solves equations with small powers of two `pow2`. *)
(*    For powers larger than 8 we'll neet a simpler way to evaluate `pow2` *) *)
(* Ltac pow2_lia:= *)
(*   try rewrite pow2_1; *)
(*   try rewrite pow2_2; *)
(*   try rewrite pow2_3; *)
(*   try rewrite pow2_4; *)
(*   try rewrite pow2_5; *)
(*   try rewrite pow2_6; *)
(*   try rewrite pow2_7; *)
(*   try rewrite pow2_8; lia. *)



(* Creates all the veriables inside ilists and vectors to apply the lemma*)
Ltac apply_IndexedSumType_Decoder_Correct' n types :=
  let types' := eval unfold types in types in 
    ilist_of_evar (fun T => DecodeM (T * ByteString) ByteString) types'
                  ltac:(fun decoders' =>
                          Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                                         ltac:(fun cache_invariants'  =>
                                                 eapply IndexedSumType_Decoder_Correct' with
                                                 (cache_invariants:= cache_invariants')
                                                 (decoders:= decoders'))).
