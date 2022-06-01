Set Nested Proofs Allowed.
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
  Ltac split_and_goal:=
    repeat (intros; match goal with
                           | |- _ /\ _ => split
                    end); intros.
Ltac inv H:= inversion H; subst. 
(* Generalization of `find_if_inside` in Common *)
Ltac find_ifopt_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X           eqn:?
  | [ |- context[If_Then_Else ?X _ _] ] => destruct X           eqn:?
  | [ |- context[If_Opt_Then_Else ?X _ _] ] => destruct X       eqn:?
  | [ H : context[if ?X then _ else _] |- _ ]=> destruct X      eqn:?
  | [ H : context[If_Then_Else ?X _ _] |- _ ]=> destruct X      eqn:?
  | [ H : context[If_Opt_Then_Else ?X _ _] |- _ ]=> destruct X  eqn:?
  end.

(* generalizations of split_and and similars*)
Ltac split_pair' :=
  repeat
    match goal with
    | H:?a * ?b
      |- _ => destruct H
    end.
Ltac split_pair :=
  split_pair';
  split_in_context prod (fun a b : Type => a) (fun a b : Type => b).
Ltac break_hyp:=
  repeat first[progress split_pair|
                progress destruct_ex|
                progress split_and].


(*! Monadic notations. *)
(*Locally rewrite this notation for `option`'s. Why don't we do it
   for all Monads!*)
Declare Scope option_scope.
Local Notation "x <- y ; z" := (Ifopt y as x Then z Else None)
                                 (at level 81, right associativity,
                                   format "'[v' x  <-  y ; '/' z ']'") : option_scope.
Local Notation "`( a , b ) <- c ; k"
  := (Ifopt c as x Then (let (a,b):= x in k) Else None)
       (at level 81, right associativity,
         format "'[v' `( a ,  b )  <-  c ; '/' k ']'") : option_scope.
Open Scope option_scope.




Section ComposedPermutationFormat.
  Definition VDecodeM V T C := T -> @CacheDecode C -> option (V * T * @CacheDecode C).


  (* F here represents all the possible projections of the elemtns of
     S. All the elemtns of (F s .) should be permutations of one another.
     Vs should contain all the types in the record S.
   *)
  

  Definition Permutation_Format {S T cache} {n} {monoid: Monoid T}  
             (Vs: Vector.t Type n)
             (*format_index: @FormatM (Fin.t n) T cache*)
             (* Format to encode Sumtypes togther with their indices *)
             (format_indexed_SumType: @FormatM (SumType Vs) T cache)
             (*Formats are subsumed by the indexed sumtype*)
             (*formats : ilist (B:=fun V => @FormatM V T cache) Vs*)
             (F: S -> list (SumType Vs) -> Prop):
    FormatM S T:= Compose_Format (format_list format_indexed_SumType) F.
 
  Definition Permutation_Format' { T cache} {n} {monoid: Monoid T}  
             (Vs: Vector.t Type n)
             (formats : ilist (B:=fun V => @FormatM V T cache) Vs):
    FormatM (list (SumType Vs)) T:= format_list (format_SumType Vs formats).

  Definition TotEncodeM:= fun (S T : Type) (store : Cache) => S -> CacheFormat -> (T * CacheFormat).
  
  Definition is_smaller (i n: nat):=
    match lt_dec i n with
    | right _ => None
    | left HH => Some HH
    end.
  
  Definition Permutation_Encode {S T cache} {n} {monoid: Monoid T} 
             (Vs: Vector.t Type n)
             (encoders : ilist (B:=fun V => TotEncodeM V T cache) Vs)
             (F: S -> list (SumType Vs)):
    TotEncodeM S T cache:=
    fun s => encode_list (encode_SumType Vs encoders) (F s).

  Definition decode_indexed_SumType {B C} {m}
             (types : Vector.t Type m) 
             (Idx : B -> @CacheDecode C -> option nat)
             (decoders : ilist (B := fun V => B -> CacheDecode -> option (V * B * CacheDecode)) types)
             (b : B)
             (cd : CacheDecode)
    : option (SumType types * B * CacheDecode):=
    i <- Idx b cd;
    HH <- is_smaller i m;
  decode_SumType types decoders (Fin.of_nat_lt HH) b cd.

  (* Correctness of aligned encoder *)
  Definition SumTypeEncoder
             {n : nat}
             {cache: Cache}
        {Vs : Vector.t Type n}
        (formats : ilist Vs)
        (encoders : ilist(B:=fun Si => forall sz : nat, @AlignedEncodeM _ Si sz) Vs)
        Encoders_Correct :=
    projT1 (CorrectAlignedEncoderForFormatSumType'
              formats encoders
              Encoders_Correct).
  Definition format_list_SumType {n : nat}
             (cache: Cache)
             {Vs : Vector.t Type n}
             (formats : ilist Vs) := format_list (format_SumType Vs formats).
      
  Definition AlignedEncodePremutation {S n C} {Vs: Vector.t Type n} (f: S -> list (SumType Vs))
    (*aligned_encoders : ilist(B:=fun Si => forall sz : nat, @AlignedEncodeM C Si sz) Vs*)
    (*A way to encode Sumtypes together with their index.*)
             (AlignedEncodeIndexedSumType: forall sz: nat, @AlignedEncodeM C (SumType Vs) sz) 
: (forall sz : nat, AlignedEncodeM sz) :=
      (Projection_AlignedEncodeM
         (AlignedEncodeList AlignedEncodeIndexedSumType) f).
  
  Lemma CorrectAlignedEncoderForFormatPermutation
        (S : Type)
        (cache : Cache)
        (n : nat)
        (Vs : Vector.t Type n)
        (*formats : ilist(B:= fun S:Type => FormatM S ByteString) Vs*)
        (*format_index: @FormatM (Fin.t n) ByteString cache*)
        (format_indexed_SumType: FormatM (SumType Vs) ByteString)
        (AlignedEncodeIndexedSumType: forall sz: nat, @AlignedEncodeM cache (SumType Vs) sz)
        (IndexedSumType_Encoder_Correct: CorrectAlignedEncoder format_indexed_SumType AlignedEncodeIndexedSumType)
        (aligned_encoders : ilist(B:=fun Si => forall sz : nat, @AlignedEncodeM _ Si sz) Vs)
        (f : S -> list (SumType Vs))
        (F : S -> list (SumType Vs) -> Prop)
        (*individual encoders correct*)
        (*Encoders_Correct: forall idx : Fin.t n,
            CorrectAlignedEncoder (ith formats idx) (ith aligned_encoders idx)*)
        (* f refines F *)
        (Correct_Projection1 : forall s x, f s = x -> F s x)
        (* The things that can be formated in F can be formated in f *)
        (Correct_Projection2 :  forall s env x v,
            F s x -> format_list format_indexed_SumType x env ∋ v ->
           exists x' v',
             format_list format_indexed_SumType x' env ∋ v' /\ f s = x')
        (* Once an element is encoded, the tail can still be FORMATED
        with the resulting environment*)
        (encode_A_OK:
          let encodeIndexedSumType := projT1 IndexedSumType_Encoder_Correct  in
          forall (a : SumType Vs) (l : list (SumType Vs)) (env : CacheFormat)
           (tenv' tenv'' : ByteString * CacheFormat),
            format_indexed_SumType a env ∋ tenv' ->
            format_list format_indexed_SumType l (snd tenv') ∋ tenv'' ->
            exists tenv3 tenv4 : ByteString * CacheFormat,
              encodeIndexedSumType a env = Some tenv3 /\
                format_list format_indexed_SumType l (snd tenv3) ∋ tenv4)
    : CorrectAlignedEncoder (Permutation_Format Vs format_indexed_SumType F)
                            (AlignedEncodePremutation f AlignedEncodeIndexedSumType).
  Proof.
    unfold Permutation_Format.

    (*Use refinement to change from composition to projection*)
    eapply (refine_CorrectAlignedEncoder _ (format_list format_indexed_SumType ◦ f)).

    { (* The refinement*)
      unfold "◦", Compose_Format, refine.
      split.
      - intro. repeat rewrite unfold_computes.
        intros [? []].
        exists x; split; auto.
      - intros H v [x []].
        eapply Correct_Projection2 in H0; eauto.
        destruct H0 as (v' & s' & ? &?).
        eapply H; eexists; eauto. }

    clear Correct_Projection1 Correct_Projection2.
    eapply CorrectAlignedEncoderProjection. 

    unshelve eapply @CorrectAlignedEncoderForFormatList.

    { (*The indexed sumtype *)
      assumption.
    }
    
    
    { (*induciton for the list*)
      eapply encode_A_OK.
    }
  Qed.

  (* Now lets try to do the aligned correctness for the decoder*)
  (* We need two things:
     1. Correctness of the unaligned version
     2. Equivalence of the aligned version.   

   *)

  (*Correctness of the unaligned version*)
  Definition list_view_pred n (Vs: Vector.t Type n) (View_predicate : _ -> Prop) : nat -> list (SumType Vs) -> Prop :=
    (fun sz ls => (| ls |) = sz /\ (forall x, In x ls -> View_predicate x)).
  
      Definition sumType_pred  n
                 idx
        (types: Vector.t Type n)
        (invariants : forall idx : Fin.t n, Vector.nth types idx -> Prop):=
        (fun st : SumType types =>
          SumType_index types st = idx /\
            invariants (SumType_index types st) (SumType_proj types st)).
  Definition Permutation_decoder {n T cache} {Vs: Vector.t Type n}
        (decode_indexed_SumType: VDecodeM (SumType Vs) T cache) (sz:nat):=
    decode_list decode_indexed_SumType sz.
  
  Lemma Permutation_decode_correct
        {S T cache} {n} {monoid: Monoid T}  
        (Vs: Vector.t Type n)
        (formats : ilist (B:=fun V => @FormatM V T cache) Vs)
        (format_indexed_SumType: FormatM (SumType Vs) T)
        (decode_indexed_SumType: VDecodeM (SumType Vs) T cache)
        A_cache_inv
        View_predicate
        (decode_indexed_SumType_correct: CorrectDecoder
                                          monoid View_predicate View_predicate eq
                                          format_indexed_SumType decode_indexed_SumType
                                          A_cache_inv format_indexed_SumType)
        (F: S -> list (SumType Vs) -> Prop)
        (invariants : forall idx : Fin.t n, Vector.nth Vs idx -> Prop)
        (A_predicate : S -> Prop)
        (View_preserves_pred: forall sz s v,
            F s v ->
            A_predicate s -> list_view_pred n Vs View_predicate sz v)
    : forall sz , CorrectDecoder
               monoid
               A_predicate
               (list_view_pred _ _ View_predicate sz)
               F
               (Permutation_Format Vs format_indexed_SumType F)
               (Permutation_decoder decode_indexed_SumType sz)
               A_cache_inv
               (format_list format_indexed_SumType).
  Proof.
    unfold Permutation_Format.
    intros.
    eapply Compose_decode_correct. 2: apply View_preserves_pred. 

    eapply FixList_decode_correct.
    eassumption.
  Qed.


  


  (*Equivalence of the aligned version.*)

  Lemma AlignedDecodePermM {C : Type} cache
        (n : nat)
        (Vs : Vector.t Type n)
        (decode_indexed_SumType: VDecodeM (SumType Vs) _ cache)
        (decode_indexed_SumType_align : forall {m}, AlignedDecodeM (SumType Vs) m)
    : forall (t : list (SumType Vs) -> VDecodeM C ByteString cache)
        (t' : list (SumType Vs) -> forall {numBytes}, AlignedDecodeM C numBytes),
      (DecodeMEquivAlignedDecodeM decode_indexed_SumType (@decode_indexed_SumType_align))
      -> (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- Permutation_decoder decode_indexed_SumType n v cd;
                          t l bs cd')
           (fun numBytes => l <- ListAlignedDecodeM (@decode_indexed_SumType_align) n;
            t' l)%AlignedDecodeM%list.
  Proof. apply AlignedDecodeListM. Qed.
  
End ComposedPermutationFormat.


Section IndexedSumType.
  (*This is one way to ocnstruct indexed SumTypes, where the index is
  directly encoded in front of the encoder.

  This format does not work for XML where the index is encoded in a XML tag. 
   *)
  Open Scope format_scope.

  (*We use this proof to construct the definition
    TODO: Delete once we are sure about the definition
   *)
  Definition format_indexed_SumType' {C} n B {monoid: Monoid B}
             (types : Vector.t Type n)
             (format_index: @FormatM (Fin.t n) B C)
    (formats : ilist (B:=fun V => @FormatM V B C) types):
    SumType types -> CacheFormat -> Comp (B * CacheFormat).
  Proof.
    eapply sequence_Format.
    - (* Index *)
      eapply Projection_Format; cycle 1.
      + eapply SumType_index.
      + eapply format_index; auto.
    - (* The format *)
      unfold FormatM.
      eapply @format_SumType. auto.
  Defined.
  
  Definition format_indexed_SumType {C n B} {monoid: Monoid B}
             (types : Vector.t Type n)
             (format_index: @FormatM (Fin.t n) B C)
             (formats : ilist (B:=fun V => @FormatM V B C) types):
    SumType types -> CacheFormat -> Comp (B * CacheFormat):=
    format_index ◦ SumType_index types ++ format_SumType types formats.

  Definition AlignedEncodeIndexedSumType
             {n C}
             (aligned_index : forall sz0 : nat, @AlignedEncodeM C _ sz0)
             {types : Vector.t Type n}
             (aligned_encoders: ilist (B:=fun V => forall sz : nat, @AlignedEncodeM C V sz)types)
             (sz: nat)
    :=
    (Projection_AlignedEncodeM aligned_index (SumType_index types) sz>>
                               AlignedEncodeSumType aligned_encoders sz)%AlignedEncodeM.
  
  Lemma IndexedSumType_Encoder_Correct:
    forall {C n}
      (types : Vector.t Type n)
      (format_index: @FormatM (Fin.t n) ByteString C)
      (aligned_index: forall sz : nat, @AlignedEncodeM C (Fin.t n) sz)
      (AlignedIndexCorrect: CorrectAlignedEncoder format_index aligned_index) 
      (formats : ilist (B:=fun V => @FormatM V ByteString C)  types)
      (aligned_encoders: ilist (B:=fun V => forall sz : nat, @AlignedEncodeM C V sz)types)
      (EncodersCorrect: forall idx, CorrectAlignedEncoder (ith formats idx) (ith aligned_encoders idx))
      (Continuation: forall (s : SumType types) (env : CacheFormat)
                       (tenv' tenv'' : ByteString * CacheFormat),
          (format_index ◦ SumType_index types) s env ∋ tenv' ->
          format_SumType types formats s (snd tenv') ∋ tenv'' ->
          exists tenv3 tenv4 : ByteString * CacheFormat,
            projT1
              (CorrectAlignedEncoderProjection format_index (SumType_index types)
                                               aligned_index AlignedIndexCorrect) s env = Some tenv3 /\
              format_SumType types formats s (snd tenv3) ∋ tenv4),
      CorrectAlignedEncoder (format_indexed_SumType types format_index formats)
                            (AlignedEncodeIndexedSumType aligned_index aligned_encoders).
  Proof.
    unfold format_indexed_SumType.
    intros;
      unshelve eapply CorrectAlignedEncoderForThenC.
    - eapply CorrectAlignedEncoderProjection; eassumption.
    - eapply CorrectAlignedEncoderForFormatSumType' ; auto.
    - assumption.
  Defined.



  Lemma IndexedSumType_decode_correct
        {T cache} {n} {monoid: Monoid T}
        format_index
        (types: Vector.t Type n)
        (formats : ilist (B:=fun V => @FormatM V T cache) types)
        (decoders: ilist (B:=fun B => VDecodeM B T cache) types)
        (decode_indexed_SumType: VDecodeM (SumType types) T cache)
        A_cache_inv
        (P_inv1 : (CacheDecode -> Prop) -> Prop)
        (P_inv_cahce: P_inv1 A_cache_inv)
        (P_cache_invariants: (Fin.t n -> (CacheDecode -> Prop) -> Prop))
        (P_cache_true: forall idx : Fin.t n, P_cache_invariants idx A_cache_inv)
        (invariants : forall idx : Fin.t n, Vector.nth types idx -> Prop)
        (DecodersCorrect: forall idx0 : Fin.t n,
            CorrectDecoder monoid (fun st : Vector.nth types idx0 => invariants idx0 st)
                           (fun st : Vector.nth types idx0 => invariants idx0 st) eq 
                           (ith formats idx0) (ith decoders idx0) A_cache_inv 
                           (ith formats idx0))
        Index_View_Predicate decode_indexed
        (DecodeIndexCorrect: cache_inv_Property A_cache_inv P_inv1 ->
                             CorrectDecoder monoid Index_View_Predicate Index_View_Predicate eq format_index
                                            decode_indexed A_cache_inv format_index)
        (Invarians_OK: forall s : SumType types,
            invariants (SumType_index types s) (SumType_proj types s) ->
            Index_View_Predicate (SumType_index types s)):
    let View_predicate := (fun st : SumType types =>
                             invariants (SumType_index types st) (SumType_proj types st)) in
    let decode_indexed_SumType:= (sequence_Decode decode_indexed
                                                  (decode_SumType types decoders)) in
                                CorrectDecoder
                                   monoid
                                   View_predicate
                                   View_predicate
                                   eq
                                   (format_indexed_SumType(B:=T) types format_index formats)
                                   decode_indexed_SumType
                                   A_cache_inv
                                   (format_indexed_SumType types format_index formats).
  Proof.
    { intros; simpl.
      unfold format_indexed_SumType.
      eapply format_sequence_correct; try eassumption; try (split; eassumption).
      { (* instantiate(1:= fun idx => decode_SumType decoders idx). *)
        intros idx **.
        eapply weaken_source_pred_Proper; cycle 1.
        eapply weaken_view_predicate; cycle 1.
        + eapply SumType_decode_correct'; eauto.
        + (*Predicate implication 1 *)
          intros st; unfold impl.
          intros []; split; auto.
        + (*Predicate implication 2 *)
          intros st; unfold impl.
          intros []; split; auto. }
      }
  Qed.
    
      

    
End IndexedSumType.

Section WordSumType.
  (* We instantiate IndexedSumTypes using simpl words *)

  (* Definition fin2Word {n:nat} (sz:nat) (idx: Fin.t n): word sz := Word.natToWord sz (FinFun.Fin2Restrict.f2n idx).  *)
  (* Definition format_word_SumType {C n B} {monoid: Monoid B} *)
  (*            {cacheAddNat : CacheAdd C nat} *)
  (*            {monoidQB: QueueMonoidOpt monoid bool} *)
  (*            (sz : nat) *)
  (*            (types : Vector.t Type n) *)
  (*            (formats : ilist (B:=fun V => @FormatM V B C) types): *)
  (*   SumType types -> CacheFormat -> Comp (B * CacheFormat):=  *)
  (*     format_indexed_SumType types (format_word ◦ (fin2Word sz)) formats. *)
      
End WordSumType.























  
  
  (*Composition for combinators
    Other composition is defined for full decoders
   *)
  Definition Compose_Decode_comb {S S' T : Type} {C}
             (decode : VDecodeM S' T C)
             (g : S' -> option S) (* Transformation Function *)
    : VDecodeM S T C :=
    fun b env => `(s', t, env') <- decode b env;
              match g s' with Some s => Some (s, t, env') | None => None end.

(*   Definition Permutation_Decode {S T cache} {n} {monoid: Monoid T}   *)
(*              (Vs: Vector.t Type n) *)
(*              (Idx : T -> CacheDecode -> option nat) *)
(*              (decoders : ilist (B:=fun V => VDecodeM V T cache) Vs) *)
(*              (F': list (SumType Vs) -> option S): *)
(*     @VDecodeM S T cache:= *)
(*     Compose_Decode_comb (decode_list (decode_indexed_SumType Vs Idx decoders) n) F'. *)
    
(*   Definition Permutation_Decode' {T cache} {n} {monoid: Monoid T}   *)
(*              (Vs: Vector.t Type n) *)
(*              (Idx : T -> CacheDecode -> option nat) *)
(*              (decoders : ilist (B:=fun V => VDecodeM V T cache) Vs) *)
(*              : *)
(*     @VDecodeM (list (SumType Vs)) T cache:= *)
(*     (decode_list (decode_indexed_SumType Vs Idx decoders) n). *)

(*   (*Forget this lemma. We only care about the aligned version*) *)
(*   Lemma CorrectDecoder_Permutation {S T}{n} {C:Cache} {monoid: Monoid T} *)
(*         (Source_Predicate : S -> Prop) *)
(*         (Vs : Vector.t Type n) *)
(*         (A_predicate : (SumType Vs) -> Prop) *)
(*         (formats : ilist Vs) *)
(*         (F : S -> list (SumType Vs) -> Prop) *)
(*         (F' : list (SumType Vs) -> option S) *)
(*         (Idx : T -> CacheDecode -> option nat) *)
(*         (decoders : ilist Vs) *)
(*         (P : CacheDecode -> Prop) *)
(*     : CorrectDecoder *)
(*         monoid *)
(*         Source_Predicate *)
(*         (fun ls : list (SumType Vs) => *)
(*            (| ls |) = n /\ (forall x : (SumType Vs), In x ls -> A_predicate x)) *)
(*         F *)
(*         (Permutation_Format Vs formats F) *)
(*         (Permutation_Decode' Vs Idx decoders) *)
(*         P *)
(*         (Permutation_Format' Vs formats). *)
(*   Proof. *)
(*     unfold Permutation_Format. *)
(*     eapply Compose_decode_correct. *)
(*     - unfold Permutation_Format', Permutation_Decode'. *)
(*       eapply FixList_decode_correct. *)
(*   Abort. (* We only care about the aligned version! *) *)

  
  
      


      
(*   Lemma CorrectEncoder_permutation {n:nat} {S T cache} {monoid: Monoid T} *)
(*         (formats :  Vector.t (@FormatM S T cache) n) *)
(*         (encoders : Vector.t (@EncodeM S T cache) n) *)
(*         (correct_encoders : ForallV2 (@CorrectEncoder S T cache) _ formats encoders ) *)
(*         (consistent_encoders: long_sequence_consistentv formats encoders) *)
(*     : CorrectEncoder (long_sequence_Formatv formats) (long_sequence_encoderv encoders). *)
    
(*     Permutation_Encode {S T cache} {n} {monoid: Monoid T}  *)
(*              (Vs: Vector.t Type n) *)
(*              (encoders : ilist (B:=fun V => TotEncodeM V T cache) Vs) *)
(*              (F: S -> list (SumType Vs)): *)



(* Section MoreVectorFacts. *)
(*   Context {n:nat}. *)
(*   Import Vectors.Vector.VectorNotations. *)

(*   (*Quick local notation for Vectors as functors to make definitions readable*) *)
(*   Infix "::" := (fun x l => Vector.cons _ x _ l) (at level 60, right associativity) : vector_scope. *)
(*   Open Scope vector_scope. *)
(*   Definition seqMap {A} {B} {n}: (Vector.t (A -> B) n) -> (Vector.t A n) -> Vector.t B n:= *)
(*     Vector.map2 (fun (X : A -> B) (X0 : A) => X X0). *)

(*   (*Vector Functor*) *)
(*   Local Infix "<$>" := Vector.map (left associativity, at level 11) (*tighter than function application*) *)
(*       (*Applicative*) *)
(*       : vector_scope. *)
(*   Local Infix "<*>" := seqMap (left associativity, at level 11) (*tighter than function application*) *)
(*       : vector_scope. *)
(*   Local Infix "<∋>" := (fun a b => computes_to <$> a <*> b) (left associativity, at level 11) *)
(*       : vector_scope. *)
(* Definition pure {A n} (a:A): Vector.t A n:= Vector.const a _.   *)
(* (* Notation pure:= (fun {n} a => Vector.const a n). *) *)

(*   Definition vector_rem {A} (v: Vector.t A (S n)) (m:nat)(H: m < S n) : Vector.t A n. *)
(*   Admitted. *)
(*   (*   replace n' with ((S n' - m) + (n'- m)). *) *)
(*   (*   eapply Vector.append. *) *)
(*   (*   - eapply Vector.take; try eassumption. lia. *) *)
(*   (*   - eapply Vector.trunc; auto. lia. *) *)
(*   (* Defined. *) *)


  
(*   Fixpoint andVec {n} (v: Vector.t Prop n): Prop := *)
(*     match v with *)
(*     | Vector.nil => True *)
(*     | Vector.cons x _ v' => x /\ andVec v' *)
(*     end. *)
(*   Definition ForallV  {m A} *)
(*              (elems : Vector.t A m) *)
(*              (P: A -> Prop) *)
(*     : Prop:= andVec (P <$> elems). *)

(*   Inductive ForallV2 {A A'} (P: A -> A' -> Prop): forall n, Vector.t A n -> Vector.t A' n -> Prop:= *)
(*   | ForallV2nill : ForallV2 P 0 [] [] *)
(*   | ForallV2cons : forall n a a' v v', ForallV2 P n v v' -> P a a' -> ForallV2 P (S n) (a::v) (a'::v'). *)
(*   Arguments ForallV2 {A A'} P {n} v v'. *)
                                                                              
  
(*   Definition ForallV2_comp  {A A'} *)
(*              (elems1 : Vector.t A n) *)
(*              (elems2 : Vector.t A' n) *)
(*              (P: A -> A' -> Prop): Prop:= andVec (Vector.map2 P elems1 elems2). *)

(*     Lemma ForallV2_cons: *)
(*     forall A A' n P (a:A) (a':A') v v', *)
(*       ForallV2 (n:=S n) P (a::v) (a'::v') -> *)
(*       P a a' /\ ForallV2 P v v'. *)
(*   Proof. *)
(*     intros. inv H. split; eauto. *)
(*     clear H. clear H6. *)
(*     revert H4. *)
(*     eapply inj_pair2_eq_dec in H2; try apply PeanoNat.Nat.eq_dec. *)
(*     eapply inj_pair2_eq_dec in H5; try apply PeanoNat.Nat.eq_dec. *)
(*     subst; eauto. *)
(*   Qed. *)
  
(* End MoreVectorFacts. *)

(* (*! Permutations Σ on vectors *) *)
(* Section Permutations. *)

(*   Section BasicPermutations. *)
(*   Context {n:nat}. *)
  
(*   (*Vector permutations, by going into lists. *) *)
(*   Definition VPermutation {A n} (v1: Vector.t A n) (v2: Vector.t A n) : Prop := *)
(*     Permutation (Vector.to_list v1) (Vector.to_list v2). *)

(*   (* Type of vector permutations*) *)
(*   Definition vperm: Type := forall A n, Vector.t A n -> Vector.t A n . *)

(*   (* Type of generic permutations, dependently correct*) *)
(*   Record permT: Type:= *)
(*     { permT_sig: nat -> nat *)
(*     ; permT_inj: forall i j, i < n -> j < n -> i <> j -> permT_sig i <> permT_sig j *)
(*     ; permT_bound: forall i, i < n -> permT_sig i < n *)
(*     }. *)
(*   Definition permT_simpl: Type:= Fin.t n -> Fin.t n. *)
(*   Definition permT_proj: permT -> permT_simpl. *)
(*   Proof. *)
(*     intros ? ?. destruct H.  *)
(*     eapply (@Fin.of_nat_lt (permT_sig0 (` (Fin.to_nat H0)))). *)
(*     simpl. *)
(*     eapply permT_bound0. *)
(*     pose proof (proj2_sig (Fin.to_nat H0)); auto. *)
(*   Qed. *)

(*   (*Identity permutation *) *)
(*   Definition id_perm: *)
(*     permT := *)
(*     {| *)
(*       permT_sig   := id; *)
(*       permT_inj   := fun i j _ _ H1 => H1; *)
(*       permT_bound := fun i H => H *)
(*     |} . *)

(*   Fixpoint inv_n (f:nat -> nat) x m: nat:= *)
(*     match m with *)
(*     | O => x (* Bogus case *) *)
(*     | S m' => if PeanoNat.Nat.eq_dec (f m) x then m else inv_n f x m' *)
(*     end. *)
(*   Definition inv_perm: permT -> permT. *)
(*   Proof. *)
(*     unshelve econstructor. *)
(*     - intros x. exact (inv_n (permT_sig H) x n). *)
(*     - destruct H; simpl. *)
(*       revert permT_inj0 permT_bound0. *)
(*       induction n. *)
(*       + intros ** ?; simpl in *. *)
(*         eapply H1; eauto. *)
(*       + admit. *)
(*     - admit. *)
(*   Admitted. *)
      
(*   End BasicPermutations. *)
(*   Arguments permT n: clear implicits. *)
(*   (* This transformation moves a perm n -> perm (n+1). *)
(*      It takes a limit value m. *)
(*      * For everything that maps to something m' < m, the mapping is preserved. *)
(*      * For everything that maps to something m' => m, the mapping is preserved bupped to (m' + 1). *)
(*      *) *)
  
(*   Definition insert' (n m:nat) (sig:nat -> nat) (x:nat): nat:= *)
(*     match (lt_eq_lt_dec n x) with *)
(*     | inleft (left _) => x *)
(*     | inleft (right _) => m *)
(*     | inright _ => match (le_gt_dec m (sig x)) with *)
(*                          | left _ => S (sig x) *)
(*                          | right _ => sig x *)
(*                          end *)
(*     end. *)
(*   Definition insert {n'}(m:nat) (H:m <= n'): permT n' ->  permT (S n'). *)
(*   Proof. *)
(*     intros [sig ? ?]. unshelve econstructor. *)
(*     - exact (insert' n' m sig). *)
(*     - intros. unfold insert'. *)
(*       Ltac break_dec := *)
(*         match goal with *)
(*         | [ |- context[lt_eq_lt_dec ?x ?y] ] => destruct (lt_eq_lt_dec x y) as [[]|] eqn:? *)
(*         | [ |- context[le_gt_dec ?x ?y] ] => destruct (le_gt_dec x y) eqn:? *)
(*         end. *)
(*       repeat break_dec; eauto; try lia. *)
(*     - intros. unfold insert'. *)
(*       repeat break_dec; eauto; try lia. *)
(*       + pose proof (permT_bound0 _ l); lia. *)
(*   Qed. *)
  
(*   (* All permutations for [0..n] *) *)
(*   (* A vector (size n!) with all the permutations of size n *) *)
(*   Definition all_permutations {n} : Vector.t (permT n) (fact n).   *)
(*   Admitted. *)

(*     (* Reorders the vector `v` according to the permutation `sig`*) *)
(*     Definition vector_perm {A n} (sig: permT n) (v : Vector.t A n) : Vector.t A n. *)
(*     Admitted. *)

  
(*       Lemma vector_id_perm_eq: forall n A (v: Vector.t A n), *)
(*           vector_perm id_perm v = v. *)
(*       Admitted. *)
  
(*   (* Reorders the ilist `il` according to the permutation `sig`*) *)
(*   Definition ilist_perm {A B n} {As : Vector.t A n} *)
(*              (sig: permT n) *)
(*              (il : @ilist _ B _ As): @ilist _ B _ (vector_perm sig As).  *)
(*   Admitted. *)

  
(*   Lemma id_ilist_perm: forall A (B: A -> Type) n (As: Vector.t A n) (il:ilist(B:=B) As), *)
(*       ilist_perm id_perm il ~= il. *)
(*   Proof. *)
(*     intros. *)
(*   Admitted. *)

(*    Definition invert_perm_ilist n' {σ: permT n'} {As: Vector.t Type n'} {B}: *)
(*     ilist(B:=B) (vector_perm σ As) -> ilist(B:=B) As. *)
(*    Admitted. *)
  
(*   Definition ilist_rem {n' i} (HH: i < S n') {As: Vector.t Type (S n')} {B}: *)
(*     ilist(B:=B) As -> ilist(B:=B) (vector_rem As i HH). *)
(*   Admitted. *)

(*   (* Definition ilist_insert {n' i} (HH: i < S n') {A} {a:A} {As: Vector.t Type n'} {B}: *) *)
(*   (*   ilist(B:=B) As -> ilist(B:=B) (vector_insert As i HH). *) *)
(*   (* Admitted. *) *)
  
  
(* End Permutations. *)
(* Arguments permT n: clear implicits. *)



(* Section LongHeterSequence. *)



   
(*       (* Long sequences: sequence a vector of elements with differetn *)
(*      types.  given a vector of formats `vec format_i` the new long *)
(*      sequence combinator [format__i] applies each format in order and *)
(*      then appends them.  *) *)
(*    Fixpoint long_sequence_Format {T cache} {monoid: Monoid T} *)
(*               {m} {types: Vector.t Type m} : *)
(*               ilist (B:= fun S => @FormatM S T cache) types -> *)
(*      @FormatM (ilist (B:= id) types) T cache := *)
(*      match types as t0 in (Vector.t _ n1) return (ilist t0 -> FormatM (ilist t0) T) *)
(*      with *)
(*      | @Vector.nil _ => constant empty_Format *)
(*      | @Vector.cons _ h n1 t0 => *)
(*          fun (formats : prim_prod (FormatM h T) (ilist t0)) *)
(*              (X : prim_prod (id h) (ilist t0)) => *)
(*            prim_fst formats (prim_fst X) *)
(*                     ThenC long_sequence_Format (prim_snd formats) (prim_snd X) *)
(*      end. *)

(*    Fixpoint long_sequence_encoder {T cache} {monoid: Monoid T} *)
(*               {m} {types: Vector.t Type m} : *)
(*               ilist (B:= fun S => @EncodeM S T cache) types -> *)
(*               @EncodeM (ilist (B:= id) types) T cache:= *)
(*      match types as t0 in (Vector.t _ n1) return (ilist t0 -> EncodeM (ilist t0) T) *)
(*      with *)
(*      | @Vector.nil _ => fun _ _ c => Some (mempty, c) *)
(*      | @Vector.cons _ S' n1 t0 => *)
(*          fun (encoders : prim_prod (EncodeM S' T) (ilist t0)) *)
(*            (X : prim_prod (id S') (ilist t0)) env => *)
(*            `(t1, env') <- prim_fst encoders (prim_fst X) env; *)
(*            `(t2, env'') <- long_sequence_encoder (prim_snd encoders) (prim_snd X) env'; *)
(*            Some (mappend t1 t2, env'')                                      *)
(*    end. *)
   

(* End LongHeterSequence. *)

(* Import Vectors.Vector.VectorNotations. *)

(* Section LongHomSequence. *)


(*    (*Locally rewrite this notation for `option`'s. Why don't we do it *)
(*    for all Monads!*) *)

   
(*       (* Long sequences: sequence a vector of elements with differetn *)
(*      types.  given a vector of formats `vec format_i` the new long *)
(*      sequence combinator [format__i] applies each format in order and *)
(*      then appends them.  *) *)
(*    Fixpoint long_sequence_Formatv {n S T cache} {monoid: Monoid T} *)
(*             (formats: Vector.t (@FormatM S T cache) n): *)
(*      @FormatM S T cache := *)
(*      match formats with *)
(*      | [] => empty_Format *)
(*      | format::formats' =>  (format ++ (long_sequence_Formatv formats'))%format *)
(*      end. *)

(*    Fixpoint long_sequence_encoderv {n S T cache} {monoid: Monoid T} *)
(*               (encoders: Vector.t (@EncodeM S T cache) n): *)
(*               @EncodeM S T cache:= *)
(*      match encoders with *)
(*      | [] => fun _ env => Some (mempty, env) *)
(*      | encoder :: encoders' => *)
(*          fun ss env => pe1 <- encoder ss env; *)
(*                     pe2 <- long_sequence_encoderv encoders' ss (snd pe1); *)
(*                     Some (mappend (fst pe1) (fst pe2), (snd pe2)) *)
(*    end. *)


   
  

  

(* (* If the first format produces *some* environment that makes the *)
(*    second format (and thus the composite format) non-empty, the *)
(*    encoder must also produce an environment that makes the second *)
(*    format non-empty. *) *)
(*   Definition encoder_sequence_consistent {S S' T : Type} {cache} *)
(*              (format1 : @FormatM S T  cache) *)
(*              (format2 : @FormatM S' T  cache) *)
(*              (encode1 : EncodeM S T): Prop :=           *)
(*     forall s s' env tenv' tenv'', *)
(*       format1 s env ∋ tenv' *)
(*       -> format2 s' (snd tenv') ∋ tenv'' *)
(*       -> exists tenv3 tenv4, *)
(*           encode1 s env = Some tenv3 *)
(*           /\ format2 s' (snd tenv3) ∋ tenv4. *)
  
(*   (* If any format produces *some* environment that makes the rest of *)
(*      the format (and thus the composite format) non-empty, the *)
(*      corresponding encoder must also produce an environment that makes *)
(*      the rest of the format format non-empty. *) *)
(*   Inductive long_sequence_consistentv {S T cache} {monoid: Monoid T}: *)
(*     forall n, Vector.t (@FormatM S T cache) n *)
(*          -> Vector.t (@EncodeM S T cache) n *)
(*          -> Prop:= *)
(*   | lsc_nil:  long_sequence_consistentv 0 [] [] *)
(*   | lsc_cons: forall n format encoder formats encoders, long_sequence_consistentv n formats encoders -> *)
(*               encoder_sequence_consistent format (long_sequence_Formatv formats) encoder -> *)
(*               long_sequence_consistentv (Datatypes.S n) (format::formats) (encoder::encoders).               *)
(*   Arguments long_sequence_consistentv {_ _ _ _ n} _ _. *)

  
  
(*   Fixpoint long_sequence_consistentv_comp {S T cache n} {monoid: Monoid T} *)
(*         (formats : Vector.t (@FormatM S T cache) n) *)
(*         (encoders : Vector.t (@EncodeM S T cache) n): Prop := *)
(*     match formats in Vector.t _ n0 return Vector.t (@EncodeM S T cache) n0 -> Prop with *)
(*     | [] => fun encoders => True *)
(*     | format :: formats' => fun encoders => *)
(*                   encoder_sequence_consistent format *)
(*                                               (long_sequence_Formatv formats')  *)
(*                                               (Vector.hd encoders) /\ *)
(*                     long_sequence_consistentv_comp formats' (Vector.tl encoders) *)
(*     end encoders. *)


   
(*   Lemma CorrectEncoder_long_sequencev {n:nat} {S T cache} {monoid: Monoid T} *)
(*         (formats :  Vector.t (@FormatM S T cache) n) *)
(*         (encoders : Vector.t (@EncodeM S T cache) n) *)
(*         (correct_encoders : ForallV2 (@CorrectEncoder S T cache) _ formats encoders ) *)
(*         (consistent_encoders: long_sequence_consistentv formats encoders) *)
(*     : CorrectEncoder (long_sequence_Formatv formats) (long_sequence_encoderv encoders). *)
(*   Proof. *)
(*     intros. *)
(*     split; intros. *)
(*     - revert b env xenv H. induction consistent_encoders. *)
(*       + simpl; intros. inv H. reflexivity. *)
(*       + eapply ForallV2_cons in correct_encoders; split_and. *)
(*         simpl; intros. *)
(*         computes_to_inv. *)
(*         find_ifopt_inside; simpl in *; try discriminate. *)
(*         destruct p; simpl in *. *)
(*         find_ifopt_inside; simpl in *; try discriminate. *)
(*         inv H0; clear H0. *)
(*         unfold sequence_Format, compose. *)
(*         destruct p. *)
(*         computes_to_econstructor. *)

(*         * (*for the fst encoder*) *)
(*           eapply H3; eauto. *)
          
(*         * (* For the rest of the encoders *)  *)
(*           computes_to_econstructor. *)
(*           eapply IHconsistent_encoders; simpl; eauto. *)
(*           inv H2. simpl in *. reflexivity. *)
(*     - revert b env xenv H. induction consistent_encoders. *)
(*       + simpl; intros. inv H.  *)
(*       + eapply ForallV2_cons in correct_encoders; split_and. *)
        
(*         simpl; intros ** computes; unfold sequence_Format, compose in *; simpl in *. *)
(*         find_ifopt_inside; simpl in *; cycle 1. *)
(*         * (* When the first encoder fails *) *)
(*           unfold compose, Bind2 in *; computes_to_inv. *)
(*           split_pair. *)
(*           eapply H0; eauto. *)
(*         * (* When the first encoder succeeds *) *)
(*           split_pair. *)
(*           find_ifopt_inside; simpl in *; try discriminate. *)
(*           unfold compose, Bind2 in *; computes_to_inv. *)
(*           edestruct H; eauto. *)
(*           break_hyp. *)
(*           rewrite Heqo in H4; injections. *)
(*           eapply IHconsistent_encoders; eauto. *)
(*   Qed. *)

(*    (** Decoder for joining long sequences. *) *)
(*    Definition long_sequence_decodev' (n':nat){T C} {monoid: Monoid T} *)
(*            (types: Vector.t Type n') *)
(*            (decoders: ilist (B:=fun V => VDecodeM V T C) types) *)
(*      : VDecodeM (ilist (B:=id) types) T C. *)
(*    Proof. *)
(*      revert types decoders. *)
(*      induction n'. *)
(*      - intros ** ??. apply Some; repeat split; try assumption. *)
(*        dependent inversion types. *)
(*        eapply inil. *)
(*      - intros types. *)
(*        dependent inversion types; subst. *)
(*        intros ** ??. *)
(*        destruct decoders. *)
(*        eapply If_Opt_Then_Else; [ | | exact None]. *)
(*        + eapply prim_fst; try assumption. *)
(*        + clear X X0. intros [[]].  *)
(*          eapply If_Opt_Then_Else; [ | | exact None]. *)
(*          * eapply (IHn' t prim_snd t0 c). *)
(*          * intros [[]]. apply Some. *)
(*            repeat split; try assumption. *)
(*    Defined. *)
         
(*    Fixpoint long_sequence_decodev {n':nat}{T C} {monoid: Monoid T} *)
(*             (types: Vector.t Type n'): *)
(*      ilist (B:=fun V => VDecodeM V T C) types *)
(*      -> VDecodeM (ilist (B:=id) types) T C:= *)
(*      match types as Ts return *)
(*            ilist (B:=fun V => VDecodeM V T C) Ts *)
(*            -> VDecodeM (ilist (B:=id) Ts) T C with *)
(*      | [] => fun _ t env => Some (inil,t,env) *)
(*      | V::Vs => fun decoders t env => *)
(*                 `(v,t',env') <- prim_fst decoders t env; *)
(*                 `(vs,t'',env'') <- long_sequence_decodev Vs (prim_snd decoders) t' env'; *)
(*                 Some (icons v vs, t'', env'') *)
(*    end. *)

(*    Definition addType {n}{types:Vector.t Type n}(A:Type) (v:SumType types): SumType (A::types):= *)
(*      match types as t in (Vector.t _ n0) return (SumType t -> SumType (A :: t)) with *)
(*      | [] => fun v0 : SumType [] => let X := match v0 return (SumType [A]) with *)
(*                                       end in X *)
(*      | @Vector.cons _ h n0 types0 => fun v0 : SumType (h :: types0) => inr v0 *)
(*      end v. *)
   
(*    Definition vectSumType_cons {n' nT} {types: Vector.t Type nT} *)
(*               {A:Type} (a:A) *)
(*               (v: Vector.t (SumType types) n'): *)
(*      Vector.t (SumType (A::types)) (S n'):= *)
(*      inj_SumType (A :: types) Fin.F1 a :: Vector.map (addType A) v. *)
   
(*    Fixpoint long_sequence_decode_sum {n':nat}{T C} {monoid: Monoid T} *)
(*            (types: Vector.t Type n') *)
(*      : ilist (B:=fun V => VDecodeM V T C) types *)
(*        -> VDecodeM (Vector.t (SumType types) n') T C:= *)
(*      match types as types in Vector.t _ n0 return *)
(*            ilist (B:=fun V => VDecodeM V T C) types *)
(*            -> VDecodeM (Vector.t (SumType types) n0) T C with *)
(*      | [] => fun _ t env => Some ([],t,env) *)
(*      | V::Vs => fun decoders t env => *)
(*                 `(v,t',env') <- prim_fst decoders t env; *)
(*                 `(vs,t'',env'') <- long_sequence_decode_sum Vs (prim_snd decoders) t' env'; *)
(*                 Some (vectSumType_cons v vs, t'', env'') *)
(*    end. *)
   
   
(*    (* Add functor Local notation for ilist *) *)
(*    Declare Scope ilist_scope. *)
   
(*    Fixpoint imap2 {A n} {B1 B2 B3 : A -> Type} (f : forall a, B1 a -> B2 a -> B3 a) {As : Vector.t A n} *)
(*     : ilist As -> ilist As -> ilist As := *)
(*     match As return ilist As -> ilist As -> ilist As with *)
(*     | [] => fun il il' => inil *)
(*     | a :: As' => fun il il' => icons (@f a (ilist_hd il) (ilist_hd il')) (imap2 f (ilist_tl il) (ilist_tl il')) *)
(*     end. *)
(*   Local Infix "<$>" := imap (left associativity, at level 11) (*tighter than function application*) *)
(*       (*Applicative*) *)
(*       : ilist_scope. *)
(*    Definition imapSeq n {B1 B2} {As: Vector.t Type n} (F: ilist (B:= fun t => B1 t -> B2 t) As) *)
(*               (X: ilist (B:=B1) As):ilist (B:=B2) As:= *)
(*      imap2 (fun (a : Type) (X0 : B1 a -> B2 a) => X0) F X. *)
(*   Local Infix "<*>" := imapSeq (left associativity, at level 11) (*tighter than function application*) *)
(*       : ilist_scope. *)
(*    Open Scope ilist_scope. *)

(*    Set Printing Implicit. *)
(*    (* Lemma Long_sequence_decode_correct *) *)
(*    (*       {S T C} {monoid:Monoid T} *) *)
(*    (*       {n:nat} *) *)
(*    (*       {P : CacheDecode -> Prop} *) *)
(*    (*       (Vs: Vector.t Type n) *) *)
(*    (*       (formats: Vector.t (@FormatM S T C) n) *) *)
(*    (*       {P_invs: Vector.t ((CacheDecode -> Prop) -> Prop) n} *) *)
(*    (*       (P_inv_pf : cache_inv_Property P (fun P => ForallV P_invs (fun P_inv => P_inv P))) *) *)
(*    (*       (views : ilist (B:= fun V => S -> V -> Prop) Vs) *) *)
(*    (*       (View_formats: ilist (B:=fun V => @FormatM V T C) Vs) *) *)
(*    (*       (decoders: ilist (B:=fun V => VDecodeM V T C) Vs) *) *)
(*    (*       (Source_Predicate: S -> Prop) *) *)
(*    (*       (View_Predicates : ilist (B:=fun V => V -> Prop) Vs) *) *)
(*    (*       (consistency_predicates : ilist (B:= fun V => V -> S -> Prop) Vs) *) *)
(*    (*       (Correct_decoders : *) *)
(*    (*         (fun view_pred__i *) *)
(*    (*           view__i *) *)
(*    (*           formats__i  *) *)
(*    (*           decoder__i *) *)
(*    (*           view_formats__i => *) *)
(*    (*         CorrectDecoder monoid Source_Predicate *) *)
(*    (*                        view_pred__i *) *)
(*    (*                        view__i *) *)
(*    (*                        formats__i  *) *)
(*    (*                        decoder__i *) *)
(*    (*                        P *) *)
(*    (*                        view_formats__i) <$> *) *)
(*    (*                                       View_Predicates <*> *) *)
(*    (*                                       views <*> *) *)
(*    (*                                       formats <*> *) *)
(*    (*                                       decoders <*> *) *)
(*    (*                                       View_formats) *) *)
(*    (*   : CorrectDecoder *) *)
(*    (*       monoid *) *)
(*    (*       Source_Predicate *) *)
(*    (*       View_Predicate *) *)
(*    (*       eq *) *)
(*    (*       (long_sequence_Formatv formats)  *) *)
(*    (*       (long_sequence_decodev Vs decoders) *) *)
(*    (*       P *) *)
(*    (*       (long_sequence_Formatv formats). *) *)

(* End LongHomSequence. *)







(* (*! Format for permutations Σ *) *)
(* Section HomReorder. *)
(*   Context (n:nat). *)

(*   (*! Format *) *)
(*   (** A permutation format is just a sequence of the reordered formats: *)

(*       Given a vector of formats [format__i] and a permutation σ *)
(*             Σ σ [format__i] ≡ Seq [format__{σ i}]  *)
(*    *) *)
(*   Definition Permutation_Format {S T cache} {monoid: Monoid T}   *)
(*              (formats : Vector.t (@FormatM S T cache) n): *)
(*     FormatM S T := *)
(*     fun s env benv => exists (σ:permT n), long_sequence_Formatv (vector_perm σ formats) s env ∋ benv. *)

(*   (*! Encoder *) *)
(*   (**  The premutation encoder is trivial: *)

(*        The encoder just encodes the sequence in order, because the *)
(*        identity is a permutation *)

(*    *) *)
(*   Definition Permutation_Encode  {S T cache} {monoid: Monoid T} *)
(*              (encoders : Vector.t (EncodeM S T) n) *)
(*     : @EncodeM S T cache := *)
(*     long_sequence_encoderv encoders. *)


(*   (** Encoder correctness *) *)
(*   Lemma CorrectEncoder_Reorder {S T cache} {monoid: Monoid T} *)
(*         (formats :  Vector.t (@FormatM S T cache) n) *)
(*         (encoders : Vector.t (@EncodeM S T cache) n) *)
(*         (correct_encoders : ForallV2 (@CorrectEncoder S T cache) _ formats encoders ) *)
(*         (consistent_encoders: long_sequence_consistentv _ formats encoders) *)
(*         (permutation_invariant: forall (σ:permT _) a b env env', *)
(*             long_sequence_Formatv (vector_perm σ formats) a env ∋ (b,env') -> *)
(*             exists b' env'', long_sequence_Formatv formats a env ∋ (b', env'')) *)
(*     : CorrectEncoder (Permutation_Format formats) (Permutation_Encode encoders). *)
(*   Proof. *)
(*     unfold CorrectEncoder, Permutation_Format, Permutation_Encode. *)
(*     intros. split; intros. *)
(*     - exists id_perm. *)
(*       rewrite vector_id_perm_eq. *)
(*       eapply CorrectEncoder_long_sequencev; eauto. *)
(*     - simpl; intros ** [σ HH]. *)
(*       eapply (permutation_invariant σ) in HH. *)
(*       break_hyp. *)
(*       eapply CorrectEncoder_long_sequencev in H; eauto. *)
(*   Defined. *)


(*   (*! Decoder*) *)

(*   (** The "ideal decoder" is not realistic, but it's easy to prove correct. *)
(*       It should be equivalent to the "real decoder" below. *)
(*    *) *)
(*   Set Printing Implicit. *)
(*   Definition permTT (n':nat): Type. *)
(*     eapply (permT n'). *)
(*   Defined. *)
(*   Definition Permutation_Decode_easy  (n':nat){T C} {monoid: Monoid T} *)
(*            (readPerm : T -> @CacheDecode C -> option (permT n')) *)
(*            (types: Vector.t Type n') *)
(*            (decoders: ilist (B:=fun V => VDecodeM V T C) types) *)
(*     : VDecodeM (Vector.t (SumType types) n'* permTT n') T C:= *)
(*     fun t env => *)
(*       σ <- readPerm t env; *)
(*       `(vs, t', env') <- long_sequence_decode_sum types decoders t env; *)
(*       Some ((vs, σ), t', env'). *)

(*   (** The "Real decoder" *) *)
(*   Let ltle {n m} := PeanoNat.Nat.lt_le_incl n m. *)
(*   Definition perm_nil: permT 0. *)
(*   Proof. *)
(*     unshelve econstructor. *)
(*     - exact id. *)
(*     - lia. *)
(*     - lia. *)
(*   Defined. *)

(*   (* partial maps*) *)
(*   Definition pmap:= nat -> option nat. *)
(*   Definition pmempty:pmap:=constant None. *)
(*   Definition pm_insert (n i:nat)(pm:pmap): pmap:= *)
(*     fun x => if PeanoNat.Nat.eq_dec x n then Some i else pm x. *)
            
(*   Fixpoint Permutation_Decode_interior (nT n':nat){T C} {monoid: Monoid T} *)
(*            (Idx : T -> @CacheDecode C -> option nat) *)
(*            (types: Vector.t Type nT) *)
(*            (decoders: ilist (B:=fun V => VDecodeM V T C) types) *)
(*     : VDecodeM (Vector.t (SumType types) n' * pmap) T C:= *)
(*     match n' with *)
(*     | 0 => fun _ _ t env => Some (([],pmempty), t, env) *)
(*     | S m =>  fun types decods t env => *)
(*                i <- Idx t env; *)
(*                HH <- is_smaller i nT; *)
(*                `(v,t',env') <- decode_SumType types decods (Fin.of_nat_lt HH) t env; *)
(*                `(vsσ,t'',env'') <- Permutation_Decode_interior nT m Idx types decods t env; *)
(*   let (vs,pm):= vsσ in *)
(*   Some ((v::vs, pm_insert (S m) i pm),t',env') *)
(*      end types decoders. *)

(*   (* Lemma CorrectDecoder_Reorder3 {S T C} {monoid: Monoid T} *) *)
(*   (*       (formats :  Vector.t (@FormatM S T C) n) *) *)
(*   (*       (decoders : Vector.t (@VDecodeM S T C) n) *) *)
(*   (*       Ps Pv Pinv Idx *) *)
(*   (*       (correct_encoders : ForallV2 *) *)
(*   (*                             (fun form dec => *) *)
(*   (*                                CorrectDecoder monoid Ps Pv eq form dec Pinv form) *) *)
(*   (*                             formats decoders) *) *)
(*   (*   : CorrectDecoder monoid *) *)
(*   (*       Ps Pv eq *) *)
(*   (*       (Permutation_Format formats) *) *)
(*   (*       (Permutation_Decode Idx _ decoders) Pinv (Permutation_Format formats). *) *)
(*   (* Proof. *) *)
(*     (* unfold CorrectDecoder, Permutation_Format, Permutation_Decode. *) *)
(*     (* intros. split; intros. *) *)
(*     (* - rewrite unfold_computes in H1. *) *)
(*     (*   destruct H1 as [σ H1]. *) *)
(*     (*   induction n. *) *)
(*     (*   + simpl in H1. *) *)
(*     (*     exists id_perm. *) *)
(*     (*   rewrite vector_id_perm_eq. *) *)
(*     (*   eapply CorrectEncoder_long_sequencev; eauto. *) *)
(*     (* - simpl; intros ** [σ HH]. *) *)
(*     (*   eapply (permutation_invariant σ) in HH. *) *)
(*     (*   break_hyp. *) *)
(*     (*   eapply CorrectEncoder_long_sequencev in H; eauto. *) *)

(* End HomReorder. *)






















(* (*! START NEWISH OLD *) *)
(* Section HeteReorder. *)
(*   Context (n: nat). *)
(*   Context (types : Vector.t Type n). *)
(*   Context (V: ilist(B:=id) types).          *)



  
(*   (* Permutation format: Fiven a list of formats [format__i] and a permutation σ, the new format *)
(*      σ[format] applies the formats in the order given by σ and then appends them.  *)
(*    *) *)
(*   Definition Permutation_Format' {T cache} {monoid: Monoid T}   *)
(*              (formats : ilist (B:= fun S => @FormatM S T cache) types)   *)
(*              (sig: @permT n): *)
(*     @FormatM (ilist (B:= id) (vector_perm sig types)) T cache:= *)
(*     long_sequence_Format (ilist_perm sig formats).  *)

(*   (* Given a heterogeneous list of Formats, produces a new list with all the permutations of the original. *)
(*      all_perm [format__i]  ≡ [ σ[format__i] | ∀ σ: permutation ] *)
(*    *) *)
(*   Definition all_permutation_formats{T cache} {monoid: Monoid T}   *)
(*              (formats : ilist (B:= fun S => @FormatM S T cache) types): *)
(*     ilist (B:= fun sig  => ilist (B:= fun S => @FormatM S T cache) (vector_perm sig types)) (@all_permutations n). *)
(*   Admitted. *)
  

(*   (** Failed definition *)
(*     Σ [format__i]  ≡ ∪ all_perm [format__i]  *)
(*                  ≡ ∪__{\forall σ}  σ[format__i] *)
(*     Fails becuase the SumType combinator expects a vector of types, *)
(*     and all_perm has a vector of permutations. *)
(*    *) *)
(*   (*Definition All_Permutation_Format {T cache} {monoid: Monoid T}   *)
(*              (formats : ilist (B:= fun S => @FormatM S T cache) types):= *)
(*     format_SumType (all_permutations n) (all_Permutation_Formats formats). *) *)


(* End HeteReorder. *)


(* (* We attempt a similar things with heterogeneous list *) *)
(* Section HomReorder. *)
(*   Context (n: nat).          *)

(*   (* Long sequences: sequence a vector of elements. Given a vector of *)
(*      formats `vec format_i` the new long sequence combinator [format__i] *)
(*      applies each format in order and then appends them.  *) *)
(*    Fixpoint list_sequence_Format {S T cache} {monoid: Monoid T} *)
(*             {m} *)
(*      (formats: Vector.t (FormatM S T) m): *)
(*      @FormatM (Vector.t S m) T cache := *)
(*        match formats in (Vector.t _ n) return (Vector.t S n -> _) with *)
(*        | Vector.nil => empty_Format *)
(*        | Vector.cons format m' formats' => *)
(*            fun (ss :  Vector.t S (Datatypes.S m')) => *)
(*              format (Vector.hd ss) ThenC (list_sequence_Format formats' (Vector.tl ss)) *)
(*        end. *)

(*   (* Permutation format: Fiven a list of formats [format__i] and a permutation σ, the new format *)
(*      σ[format] applies the formats in the order given by σ and then appends them.  *)
(*    *) *)
(*   Definition hom_Permutation_Format {S T cache} {monoid: Monoid T}   *)
(*              (formats : Vector.t (@FormatM S T cache) n) *)
(*              (sig: permT n): *)
(*     @FormatM (Vector.t S n) T cache:= *)
(*     list_sequence_Format (vector_perm sig formats).  *)

  
  
(*   (* Given a homogeneous list of Formats, produces a new list with all the permutations of the original. *)
(*      all_perm [format__i]  ≡ [ σ[format__i] | ∀ σ: permutation ] *)
(*    *) *)
(*   Definition all_permutation_formats' {S T cache} {monoid: Monoid T} *)
(*              (formats : Vector.t (@FormatM S T cache) n): *)
(*     Vector.t (FormatM (Vector.t S n) T) (fact n):= *)
(*     (hom_Permutation_Format formats <$> all_permutations). *)

(*   Definition Union {S T A m cache} (dom : Vector.t A m)  (f: A -> @FormatM S T cache): @FormatM S T cache:= *)
(*     Union_Format (f <$> dom). *)

(*   Notation "'U{' f | x '∈' dom '}'" := (Union dom (fun x => f)) *)
(*     (at level 70).  *)
  
(*   (** Definition *)
(*     Σ [format__i]  ≡ ∪ all_perm [format__i]  *)
(*                  ≡ ∪__{\forall σ}  σ[format__i] *)
(*     Fails becuase the SumType combinator expects a vector of types, *)
(*     and all_perm has a vector of permutations. *)
(*    *) *)
(*   Definition All_Permutation_Format {S T cache} {monoid: Monoid T}   *)
(*              (formats : Vector.t (@FormatM S T cache) n): *)
(*     FormatM (Vector.t S n) T:= *)
(*     U{ hom_Permutation_Format formats x | x ∈ all_permutations }. *)

(* End HomReorder. *)


(* Section HeteReorder2. *)
(*   Context (n:nat). *)
(*   (* In this section we don't attempt to go by basic combinators. *)

(*    Then see if we can split it. *)
(*    *) *)
(*   Definition Permutation_Format2 {T cache} {monoid: Monoid T}   *)
(*              (types : Vector.t Type n) *)
(*              (formats : ilist (B:= fun S => @FormatM S T cache) types): *)
(*     FormatM (ilist (B:=id) types) T := *)
(*     fun il env benv => exists σ, long_sequence_Format (ilist_perm σ formats) (ilist_perm σ il) env ∋ benv. *)

(*   Definition Permutation_Encode2  {T cache} {monoid: Monoid T} *)
(*              (types : Vector.t Type n) *)
(*              (encoders : ilist (B:= fun S => EncodeM S T) types) *)
(*     : @EncodeM (ilist (B:= id) types) T cache := *)
(*     long_sequence_encoder encoders. *)

(*   (*   Definition Compose_Decode {T cache} {monoid: Monoid T} *) *)
(*   (*            (types : Vector.t Type n) *) *)
(*   (*            (decoders : ilist (B:= fun S => DecodeM S T) types) *) *)
(*   (*   : DecodeM S T  := *) *)
(*   (*   fun b env => `(s, env') <- decode b env; Some (g s, env'). *) *)

  
(*   (* Definition Permutation_Decoder2  {T cache} {monoid: Monoid T} *) *)
(*   (*            (types : Vector.t Type n) *) *)
(*   (*            (encoders : ilist (B:= fun S => EncodeM S T) types) *) *)
(*   (*   : @EncodeM (ilist (B:= id) types) T cache := *) *)
(*   (*   long_sequence_encoder encoders. *) *)
  
(*   (*Vector Functor*) *)
 
  
(*   Fixpoint constantIlist {T n A} *)
(*              {As : Vector.t A n} *)
(*              (constList : ilist (B:= constant T) As) *)
(*     : Vector.t T n:= *)
(*     match As in Vector.t _ n0 return ilist As -> Vector.t T n0 with *)
(*     | [] => fun il => [] *)
(*     | a :: As' => fun il => (ilist_hd il) :: constantIlist (ilist_tl il) *)
(*     end constList. *)
(*   (* joins ilists of Prop *) *)
(*   Definition andIlist {A m} {As: Vector.t A m} il:=  andVec (constantIlist (As:=As) il). *)

(*   Definition ForallI  {m A} *)
(*              {B: A -> Type} *)
(*              {As : Vector.t A m} *)
(*              (elems : ilist (B:= B) As) *)
(*              (P: forall a, B a -> Prop) *)
(*     : Prop:= andIlist (imap P elems). *)

    
(*   Fixpoint imap2 {A n} {B1 B2 B3 : A -> Type} (f : forall a, B1 a -> B2 a -> B3 a) (As : Vector.t A n) *)
(*     : ilist As -> ilist As -> ilist As := *)
(*     match As return ilist As -> ilist As -> ilist As with *)
(*     | [] => fun il il' => inil *)
(*     | a :: As' => fun il il' => icons (@f a (ilist_hd il) (ilist_hd il')) (imap2 f As' (ilist_tl il) (ilist_tl il')) *)
(*     end. *)
  
(*   Definition ForallI2  {m A} *)
(*              {B1 B2: A -> Type} *)
(*              {As : Vector.t A m} *)
(*              (elems1 : ilist (B:= B1) As) *)
(*              (elems2 : ilist (B:= B2) As) *)
(*              (P: forall a, B1 a -> B2 a -> Prop): Prop:= andIlist (imap2 P _ elems1 elems2). *)
  
  
(*   (* If any format produces *some* environment that makes the rest of *)
(*      the format (and thus the composite format) non-empty, the *)
(*      corresponding encoder must also produce an environment that makes *)
(*      the rest of the format format non-empty. *) *)
(*   Fixpoint long_sequence_consistent {T cache n} {monoid: Monoid T} *)
(*         (As : Vector.t Type n) *)
(*         (formats : ilist (B:= fun S => @FormatM S T cache) As) *)
(*         (encoders' : ilist (B:= fun S => @EncodeM S T cache) As): Prop := *)
(*     match As in Vector.t _ n0 return ilist As -> ilist (B:= fun S => @EncodeM S T cache) As -> Prop with *)
(*     | [] => fun formats encoders => True *)
(*     | a :: As' => fun formats encoders => *)
(*                   encoder_sequence_consistent (prim_fst formats) *)
(*                                               (long_sequence_Format (prim_snd formats))  *)
(*                                               (prim_fst encoders) /\ *)
(*                     long_sequence_consistent As' (prim_snd formats) (prim_snd encoders) *)
(*     end formats encoders'. *)
  
(*   Lemma CorrectEncoder_long_sequence {T cache} {monoid: Monoid T} *)
(*         (types : Vector.t Type n) *)
(*         (formats : ilist (B:= fun S => @FormatM S T cache) types) *)
(*         (encoders : ilist (B:= fun S => EncodeM S T) types) *)
(*         (correct_encoders : ForallI2 formats encoders (fun a b1 b2 => @CorrectEncoder a T cache b1 b2) ) *)
(*         (consistent_encoders: long_sequence_consistent types formats encoders) *)
(*     : CorrectEncoder (long_sequence_Format formats) (long_sequence_encoder encoders). *)
(*   Proof. *)
(*     split; intros. *)
(*     - revert b env H; induction types. *)
(*       + simpl in *. intros b env H. inversion H; subst. *)
(*         rewrite unfold_computes. *)
(*         reflexivity. *)
(*       + simpl in *. intros b env H.  *)
(*         find_ifopt_inside; try solve[inversion H]. *)
(*         destruct p; simpl in H.  *)
(*         find_ifopt_inside; try solve[inversion H]. *)
(*         destruct p; simpl in H. *)
(*         inversion H; subst. *)
(*         destruct correct_encoders as [correct_fst_encoder correct_encoders']. *)
(*         eapply IHtypes in Heqo0; eauto; *)
(*           try eapply consistent_encoders. *)
(*         2: eapply correct_encoders'. *)
(*         simpl in correct_fst_encoder. *)
(*         eapply correct_fst_encoder in Heqo. *)
(*         move Heqo at bottom. *)
(*         unfold compose. *)
(*         computes_to_econstructor; try eassumption. *)
(*         computes_to_econstructor; try eassumption. *)
(*         reflexivity. *)
(*     - unfold compose. revert b xenv env H; induction types. *)
(*       + simpl in *. intros b xenv env H. inversion H; subst. *)
(*       + simpl in *. intros b xenv env H computes. *)
(*         unfold compose, Bind2 in *; computes_to_inv. destruct v; destruct v0. *)
(*         destruct correct_encoders as [correct_fst_encoder correct_encoders']. *)
(*         find_ifopt_inside; (*This gives me the goals on the order I wnat them*) cycle 1. *)
(*         * (* First encoder fails*) *)
(*           eapply correct_fst_encoder; eauto. *)
(*         * (* First encoder succeeds*) *)
(*           destruct p; simpl in *. *)
          
(*           (* We use the consistency of the encoder to recover the right environment *) *)
(*           destruct consistent_encoders as [consistent_fst_encoder consistent_encoders]. *)
(*           edestruct consistent_fst_encoder; eauto. *)
(*           destruct_ex; split_and. destruct x; destruct x0. simpl in *. *)

          
(*           eapply IHtypes; eauto; *)
(*             try eapply consistent_encoders; try eapply correct_encoders'. *)
(*           find_ifopt_inside; *)
(*           (* If nothing fails, the hypothesis was wrong *) *)
(*           try solve[(destruct p; inversion H)]. *)

(*           cut (c1 = c2); [intros; subst; assumption|]. *)
(*           clear - H1 Heqo. *)
          
(*           match type of H1 with *)
(*           | ?x = _ => match type of Heqo with *)
(*                      | ?y = _ => replace x with y in H1  *)
(*                      end  *)
(*           end. *)
(*           -- rewrite H1 in Heqo; injections; reflexivity. *)
(*           -- f_equal. *)
(*   Qed. *)

(*       Lemma long_sequence_Format_Proper {T cache} *)
(*             {monoid: Monoid T}: *)
(*         forall (types types' : Vector.t Type n), *)
(*         forall (formats: ilist (B:= fun S => @FormatM S T cache) types) *)
(*           (formats': ilist (B:= fun S => @FormatM S T cache) types') *)
(*           elems elems' env benv benv', *)
(*           types = types' ->  *)
(*           formats ~= formats' -> *)
(*         elems ~= elems' -> *)
(*         benv ~= benv' ->  *)
(*         long_sequence_Format formats  elems env ∋ benv -> *)
(*         long_sequence_Format formats' elems' env ∋ benv'. *)
(*       Proof. *)

(*       Admitted. *)
      
(*   Lemma CorrectEncoder_Reorder {T cache} {monoid: Monoid T} *)
(*         (types : Vector.t Type n) *)
(*         (formats : ilist (B:= fun S => @FormatM S T cache) types) *)
(*         (encoders : ilist (B:= fun S => EncodeM S T) types) *)
(*         (correct_encoders : ForallI2 formats encoders (fun a b1 b2 => @CorrectEncoder a T cache b1 b2) ) *)
(*     : CorrectEncoder (Permutation_Format2 _ formats) (Permutation_Encode2 _ encoders). *)
(*   Proof. *)
(*     unfold CorrectEncoder, Permutation_Format2, Permutation_Encode2. *)
(*     intros. split; intros. *)
(*     - exists id_perm. *)
(*       eapply CorrectEncoder_long_sequence in H; eauto. *)
(*       assert (HH:types = vector_perm id_perm types) by admit. *)
(*       (* eapply long_sequence_Format_Proper. 5: eapply H. *) *)
(*       (* all: eauto. *) *)
(*       (* clear -HH. revert formats. *) *)

(*       (* trouble prooving *)
(*        `forall formats : ilist types, formats ~= ilist_perm id_perm formats` *)
(*        *) *)
(*       Admitted. *)

(* End HeteReorder2. *)








     
      
      





(*   HERE *)





















  


  
(* (* Start unsuccesful attempt*) *)


(* Inductive LabeledType (S:string): Type := *)
(*     | Labeled: forall {A}, A -> LabeledType S. *)

(* Definition useLabel {lbl} (lt: LabeledType lbl):= *)
(*   match lt with *)
(*   | Labeled _ a => lbl *)
(*   end. *)

(* Section Delimiter. *)
(*   Context {S : Type}. *)
(*   Context {T : Type}. *)
  
(*   Context {cFormat : Type}. *)
(*   Context {cDecode : Type}. *)
(*   Context {m:nat}. *)
(*   Context {cEquivVec : Vector.t cFormat m -> Vector.t cDecode m -> Prop}. *)
(*   Context {cEquiv : cFormat -> cDecode -> Prop}. *)
(*   Let cacheVec := Build_Cache cEquivVec. *)
(*   Let cache    := Build_Cache cEquiv. *)
  
(*   Context {monoid : Monoid T}. *)
(*   Context {monoidUnit : QueueMonoidOpt monoid bool}. *)

(*   (*Quick local notation for Vectors as functors to make definitions readable*) *)
(*   Infix "::" := (fun x l => Vector.cons _ x _ l) (at level 60, right associativity) : vector_scope. *)
(*   Open Scope vector_scope. *)
(*   Definition seqMap {A} {B} {n}: (Vector.t (A -> B) n) -> (Vector.t A n) -> Vector.t B n:= *)
(*     Vector.map2 (fun (X : A -> B) (X0 : A) => X X0). *)

(*   (*Functor*) *)
(*   Local Infix "<$>" := Vector.map (left associativity, at level 11) (*tighter than function application*) *)
(*       (*Applicative*) *)
(*       : vector_scope. *)
(*   Local Infix "<*>" := seqMap (left associativity, at level 11) (*tighter than function application*) *)
(*       : vector_scope. *)
(*   Local Infix "<∋>" := (fun a b => computes_to <$> a <*> b) (left associativity, at level 11) *)
(*       : vector_scope. *)
(*   Notation pure:= Vector.const. *)

(*   (* function composition *) *)
    
    
(*   Definition vectPair {T1 T2} (X1: Vector.t T1 m * Vector.t T2 m): *)
(*     Vector.t (T1 * T2) m:= *)
(*     let (t, c) := X1 in Vector.map2 pair t c. *)

(*   (* Makes a vector of formats into a format of vectors.  The odd *)
(*      thing here is that it "formats" into a vector of T's and not a *)
(*      T. This is not common, but [T] is still a monoid. *)

(*      Granted Vector.t is not a monoid... but kind of... Well deal with *)
(*      that later.  *) *)
(*   Definition Product_Format *)
(*              (formats : Vector.t (@FormatM S T cache) m): *)
(*     @FormatM (Vector.t S m) (Vector.t T m) cacheVec :=  *)
(*     fun (s : Vector.t S m) *)
(*         (env : @CacheFormat cacheVec) (benv' : Vector.t T m * @CacheFormat cacheVec) => *)
(*       andVec (formats <*> s <*> env <∋> vectPair benv'). *)

  
  
(*   (* From a format of vectors, produce all permutations. *)

(*      Given a format of vectors, now admits all permutations of the format.  *)
(*    *) *)
(*   Definition Hom_Reorder_Format *)
(*     (format : @FormatM (Vector.t S m) (Vector.t T m) cacheVec) *)
(*     : @FormatM (Vector.t S m) (Vector.t T m) cacheVec:= *)
(*     fun reordF env benv' => *)
(*       exists s, format s env  ∋ benv' *)
(*                 /\ VPermutation s reordF. *)

(*   (* The encoder is trivial, but we include it for completion *) *)
(*   Definition Hom_Reorder_Encoder *)
(*              (encode : @EncodeM (Vector.t S m) (Vector.t T m) cache) *)
(*     : EncodeM (Vector.t S m) (Vector.t T m) := encode. *)

(*   Definition vpermutations {n} (v : Vector.t T n): list (Vector.t T n). *)
(*   Admitted. *)
  
(*   Fixpoint firstSome {A B} (f: A -> option B) (l: list A) : option B := *)
(*     (match l with *)
(*     | [] => None *)
(*     | x::l => match f x with *)
(*               | Some y => Some y *)
(*               | None => firstSome f l *)
(*               end *)
(*     end)%list. *)
  
(*   Definition Hom_Reorder_Decoder *)
(*              (decode : @DecodeM (Vector.t S m) (Vector.t T m) cache) *)
(*     : DecodeM (Vector.t S m) (Vector.t T m) := *)
(*     fun t c => firstSome (fun x => decode x c) (vpermutations t). *)


  

(*   (* From a format of vectors to a format "vector to buffer" *)

(*     This just appends all the results. *)
(*    *) *)
(*   Fixpoint flatten_vector {n} (vt: Vector.t T n) : T:= *)
(*     match vt with *)
(*     | Vector.nil => mempty *)
(*     | Vector.cons x _ vt' => mappend x (flatten_vector vt') *)
(*     end. *)
(*   Definition Flatten_Vector_Format *)
(*              (format : @FormatM (Vector.t S m) (Vector.t T m) cacheVec) *)
(*     : @FormatM (Vector.t S m) T cacheVec:= *)
(*     fun s env tenv' => *)
(*       let (t,env') := tenv' in *)
(*       exists vt, format s env  ∋ (vt, env') *)
(*                  /\ flatten_vector vt = t. *)


(*   (* From a vector of Formats to a, format of vectors allowing *)
(*   reordering*) *)
(*   Definition Vector_Reorder_Format *)
(*              (formats : Vector.t (@FormatM S T cache) m) *)
(*     : @FormatM (Vector.t S m) T cacheVec:= *)
(*     Flatten_Vector_Format (Hom_Reorder_Format (Product_Format formats)). *)

(*     Definition Left_Compose_Format {S T T'} *)
(*                (format : @FormatM S T' cache) *)
(*                (preview: T -> T' -> Prop) *)
(*     : @FormatM S T cache:= *)
(*     fun s env benv' => *)
(*       let (t, env') := benv' in *)
(*       exists t', format s env  ∋ (t', env') *)
(*                  /\ preview t t'. *)

(*   (* The Transformation Function could be partial, *)
(*      but the correctness becomes more complicated. *)
(*    *) *)
(*   Definition Left_Compose_Encode {T T'} *)
(*              (encode : @EncodeM S T' cache) *)
(*              (f' : T' -> T) *)
(*     : EncodeM S T := *)
(*     fun s env => *)
(*       `(t, env') <- encode s env; Some ( f' t, env'). *)
                                    
(*   Definition Left_Compose_Decode {S T T'} *)
(*              (decode : @DecodeM S T' cache) *)
(*              (g : T -> T') (* Transformation Function *) *)
(*     : @DecodeM S T cache:= *)
(*     fun b env => `(s, env') <- decode (g b) env; Some (s, env'). *)

(*   Definition Left_Compose_Decode' {T T'} *)
(*              (decode : @DecodeM (S * T') T' cache) *)
(*              (g : T -> T') (* Transformation Function *) *)
(*              (gext : T' -> T) (* Transform the rest of the stream *) *)
(*     : @DecodeM (S * T) T cache:= *)
(*     fun b env => `(s, ext, env') <- decode (g b) env; Some (s, gext ext, env'). *)

(*   Lemma CorrectEncoder_Left_Compose {T'} *)
(*         (format : @FormatM S T' cache) *)
(*         (encode : @EncodeM S T' cache) *)
(*         (f : T -> T' -> Prop) *)
(*         (f' : T' -> T) *)
(*         (f'_refines_f_1 : *)
(*            forall t t', *)
(*              f' t' = t -> *)
(*              f t t') *)
(*         (f'_sound_choice : True) *)
(*     : @CorrectEncoder _ _ cache format encode *)
(*       -> CorrectEncoder (Left_Compose_Format format f) (Left_Compose_Encode encode f'). *)
(*   Proof. *)
(*     unfold CorrectEncoder. *)
(*     unfold Left_Compose_Encode, Left_Compose_Format in *; split; intros. *)
(*     - apply unfold_computes. *)
(*       destruct (encode a env) as [(?&?)|] eqn:?; simpl in *; try discriminate. *)
(*       (* destruct (f' t) eqn: ?; simpl in *; try discriminate. *) *)
(*       inversion H0; subst. *)
(*       eexists; split; eauto. *)
(*       eapply H; eauto. *)
(*     - rewrite unfold_computes. intro;  destruct_ex; split_and. *)
(*       destruct (encode a env) as [(?&?)|] eqn:?; simpl in *; try discriminate. *)
(*       eapply H4; eauto. *)
(*   Qed. *)

(*   Lemma inverses_commute: *)
(*     forall {T T'} {m: Monoid T} {m': Monoid T'} (g: T -> T') gext *)
(*         (g_inv1: forall x, gext (g x) = x) *)
(*         (g_inv2: forall x, g (gext x) = x) *)
(*         (g_mappend : forall t t', g (mappend t t') = mappend (g t ) (g t')), *)
(*         forall t t', gext (mappend t t') = mappend (gext t ) (gext t'). *)
(*   Proof. *)
(*     intros. *)
(*     specialize (g_mappend (gext t) (gext t')). *)
(*     repeat rewrite g_inv2 in g_mappend. *)
(*     rewrite <- g_mappend, g_inv1. *)
(*     reflexivity. *)
(*   Qed. *)
    
(*   (* This is a first attempt *) *)
(*   Lemma Left_Compose_decode_correct {T'} *)
(*         {P : CacheDecode -> Prop} *)
(*         (g : T -> T') *)
(*         (gext : T' -> T) *)
(*         {monoid' : Monoid T'} *)
(*         (R : T -> T' -> Prop) *)
(*         (View_Predicate : S -> Prop) *)
(*         (format : FormatM S T') *)
(*         (view_format : FormatM S T') *)
(*         (decode_V : @DecodeM (S * T') T' cache) *)
(*         (g_refines_R: *)
(*            forall t t', *)
(*              g t = t' -> *)
(*              R t t') *)
(*         (R_choice_Ok: forall s env xenv t t', *)
(*           R t t' -> *)
(*           format s env ∋ (t', xenv) -> *)
(*           format s env ∋ (g t, xenv)) *)
(*         (g_inv1: forall x, gext (g x) = x) *)
(*         (g_inv2: forall x, g (gext x) = x) *)
(*         (g_mappend : forall t t', g (mappend t t') = mappend (g t ) (g t')) *)
(*         (decode_V_OK : CorrectDecoder(S:=S)(T:=T') monoid' View_Predicate View_Predicate eq format decode_V P *)
(*                                       view_format) *)
(*   : CorrectDecoder monoid  View_Predicate View_Predicate eq *)
(*                    (Left_Compose_Format format R) (Left_Compose_Decode' decode_V g gext) *)
(*                    P (Left_Compose_Format view_format R). *)
(*   Proof. *)
(*     unfold Left_Compose_Format, Left_Compose_Decode'; simpl. *)
(*     destruct decode_V_OK as [Hsound Hconsist]; split; intros. *)
(*     - rewrite unfold_computes in H1. *)
(*       destruct H1 as (t' & Hformat & Rtt'). *)
(*       specialize (Hsound env env' xenv s (g t) (g ext) *)
(*                          ltac:(ez_apply) *)
(*                          ltac:(ez_apply) *)
(*                          ltac:(ez_apply) *)
(*                          ltac:(eapply R_choice_Ok; eauto)). *)
(*       destruct Hsound as (?&?&?&?&?&?&?); subst. *)
(*       exists x, x0. split_and_goal. *)
(*       + rewrite g_mappend, H1. *)
(*         simpl; repeat f_equal; eauto. *)
(*       + reflexivity. *)
(*       + move H3 at bottom. *)
(*         apply unfold_computes. *)
(*         exists (g t); split; eauto. *)
(*       + assumption. *)
(*       + assumption. *)
(*     - specialize (Hconsist env env' xenv' v (g t) (g t') *)
(*                          ltac:(ez_apply) *)
(*                                 ltac:(ez_apply)). *)
(*       destruct (decode_V (g t) env') as [((?&?)&?)|]eqn:?; simpl in *; try discriminate. *)
(*       inversion H1; subst. *)
(*       rewrite g_inv2 in Hconsist. *)
(*       specialize (Hconsist ltac:(reflexivity)). *)
(*       destruct Hconsist as (?&?&?&?&?&?&?). *)
(*       split; eauto. *)
(*       exists (gext x), x0. *)
(*       split_and_goal. *)
(*       + move H3 at bottom. *)
(*         apply unfold_computes. *)
(*         exists (x); split; eauto. *)
(*       + rewrite <- (g_inv1 t). *)
(*         rewrite H4. *)
(*         eapply inverses_commute; auto. *)
(*       + assumption. *)
(*       + assumption. *)
(*   Defined. *)



(*   (* Redefine the reorder using Left_Commpose*)  *)
(*   Definition Hom_Reorder_Format' *)
(*     (format : @FormatM (Vector.t S m) (Vector.t T m) cacheVec) *)
(*     : @FormatM (Vector.t S m) (Vector.t T m) cacheVec:= *)
(*     fun reordF env benv' => *)
(*       exists s, format s env  ∋ benv' *)
(*                 /\ VPermutation s reordF. *)

(*   (* The encoder is trivial, but we include it for completion *) *)
(*   Definition Hom_Reorder_Encoder *)
(*              (encode : @EncodeM (Vector.t S m) (Vector.t T m) cache) *)
(*     : EncodeM (Vector.t S m) (Vector.t T m) := encode. *)

(*   Definition vpermutations {n} (v : Vector.t T n): list (Vector.t T n). *)
(*   Admitted. *)
  
(*   Fixpoint firstSome {A B} (f: A -> option B) (l: list A) : option B := *)
(*     (match l with *)
(*     | [] => None *)
(*     | x::l => match f x with *)
(*               | Some y => Some y *)
(*               | None => firstSome f l *)
(*               end *)
(*     end)%list. *)
  
(*   Definition Hom_Reorder_Decoder *)
(*              (decode : @DecodeM (Vector.t S m) (Vector.t T m) cache) *)
(*     : DecodeM (Vector.t S m) (Vector.t T m) := *)
(*     fun t c => firstSome (fun x => decode x c) (vpermutations t). *)
        

  




(*   (* ## Left composition  *)

(*      These Lemma should generalize the Hom_Reorder_Format Lemmas *)
(*    *) *)

  













(*   (* Older stuff*) *)
(*   Definition Hom_Reorder_Format {cache} *)
(*     (formats : @FormatM (Vector.t S m) T cache) *)
(*     : @FormatM (Vector.t S m) T cache := *)
(*     Compose_Format formats VPermutation. *)

(*   (* This lemma is trivial. I added for completion.  i.e. the encoder *)
(*    before a reordering still works after a reordering, becuase *)
(*    identity is a permutation.  *) *)
(*   Definition Hom_Reorder_Encode *)
(*              {cache} *)
(*              (encode : @EncodeM (Vector.t S m) T cache) *)
(*     : EncodeM (Vector.t S m) T := encode. *)

(*   Definition Hom_Reorder_Decode *)
(*              (decode : DecodeM (Vector.t S m) T) *)
(*              : DecodeM (Vector.t S m) T  := *)
(*     fun b env => `(s, env') <- decode b env; Some (g s, env'). *)
    
  
(*   (* Homogeneous reordering, can accept the list of similarly-typed *)
(*   formats in any order*) *)
(*   Definition Hom_Reorder_Format *)
(*     (formats : list [FormatM S T]) *)
(*     : FormatM [S] [T] := *)
(*     fun s env benv' => *)
(*       exists s', format s' env ∋ benv' /\ f s s'. *)

(*   Definition Compose_Decode {S' : Type} *)
(*              (decode : DecodeM S' T) *)
(*              (g : S' -> S) (* Transformation Function *) *)
(*     : DecodeM S T  := *)
(*     fun b env => `(s, env') <- decode b env; Some (g s, env'). *)

(*   Definition Compose_Decode' {S' : Type} *)
(*              (decode : DecodeM S' T) *)
(*              (g : S' -> option S) (* Transformation Function *) *)
(*     : DecodeM S T  := *)
(*     fun b env => `(s', env') <- decode b env; match g s' with Some s => Some (s, env') | None => None end. *)

(*   Definition Compose_Encode *)
(*              {S' : Type} *)
(*              (encode : EncodeM S' T) *)
(*              (f' : S -> option S') *)
(*     : EncodeM S T := *)
(*     fun s => Ifopt f' s as s' Then encode s' Else fun _ => None. *)

 
