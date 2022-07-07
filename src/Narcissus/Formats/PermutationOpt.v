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
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.Formats.Derived.IndexedSumType.
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


(** *TEMP tactics

    Some useful exploratory tactics. Should not be used in production,
    feel free to remove once file is completed    
 *)

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

Ltac exploit_one H:=
  match type of H with
    ?T -> _ =>
      cut T;
      [ let H' := fresh in intros H';
                           specialize (H H') 
      | ]
  end.

Ltac ez_apply:=
  match goal with
    [H: _ |- _] => eapply H
  end.


(* END: TEMP tactics*)

(* Great tactic for dealing with binds
   This probably exists somwhere else.
 *)
Ltac destruct_bind_inside H:=
  eapply Bind_inv in H; destruct H as [? []].
Ltac destruct_bind:=
  lazymatch goal with
    [H : Bind2 _ _ ∋ _ |- _ ]  => destruct_bind_inside H
  | [H : Bind _ _ ∋ _ |- _ ]   => destruct_bind_inside H
  | [H:(_ ++ _ ) _ _ ∋ _ |- _] => destruct_bind_inside H
  end.

Section Resilience.
  (** *Definitions*)
  (* Formats are environment-resilient when the environment can't make
     it fail.  The either succeeds for all environmnets or fails for
     all.  The result can change based on the environment, but it
     cannot fail if it would succeed in a different environment.
     
     We distinguish resilience from agnosticism, also defined below,
     where the environment is irrelevant. *)
  Definition env_resilient {A Q} (format: FormatM A Q):=
    forall x env1 env2 r1,
      format x env1 ∋ r1 ->
      exists r2, format x env2 ∋ r2.
  (* The negation from is weaker, but appears in several context. *)
  Definition env_resilient_not {A Q} (format: FormatM A Q):=
    forall x env1 env2,
      (forall r1, format x env1 ∌ r1) ->
      forall r2, format x env2 ∌ r2.
  Definition env_agnostic {A Q} (format: FormatM A Q):=
    forall x env1 env2 r1,
      format x env1 ∋ r1 ->
      format x env2 ∋ r1.
  Lemma env_resilient_to_not:
    forall {A Q} (format: FormatM A Q),
      env_resilient format -> env_resilient_not format. 
  Proof.
    unfold env_resilient, env_resilient_not; intros.
    intros HH. 
    eapply H in HH. destruct_ex. 
    eapply H0; eauto.
  Qed.
  
  (*The oposite is also true, given the EM*)
  Lemma env_resilient_from_not:
    forall {A Q} (EM: forall P:Prop, P \/ ~P) (format: FormatM A Q),
      env_resilient_not format -> env_resilient format. 
  Proof.
    unfold env_resilient, env_resilient_not; intros * EM format Hresilient * HH.
    match goal with
      |- ?P => destruct (EM P) as [HH1|HH1]; auto
    end.
    exfalso; eapply Hresilient.
    - intros ** ?. 
      eapply LogicFacts.not_exists_forall in HH1.
      eapply HH1; eassumption.
    - eassumption.
  Qed.

  (** *Instances of resilience*)
  
  (** Base formats*)
  Lemma word_resilience:
    forall {sz}, env_resilient (format_word (sz:=sz)).
  Proof. econstructor; eapply ReturnComputes. Qed.

  Lemma format_enum_resilience:
    forall {len sz} (codes: Vector.t (word sz) (S len)), env_resilient (format_enum codes).
  Proof.
    unfold env_resilient, format_enum; simpl.
    intros *. eapply word_resilience.
  Qed.

  (** Combinators *)
  Lemma SumType_resilience:
    forall n (types: Vector.t Type n)
      (formats : ilist (B:= fun T => FormatM T ByteString) types),
    forall (Hforms_resi: forall idx, env_resilient (ith formats idx)), 
      env_resilient (format_SumType types formats).
  Proof.
    unfold format_SumType.
    unfold env_resilient.
    intros.
    eapply Hforms_resi in H as [].
    eexists; eauto.
  Qed.
  
  Lemma Projection_resilience:
    forall {A B Q:Type}
      (format : FormatM A Q)
      (Hresi: env_resilient format)
      (f: B -> A),
      env_resilient (Projection_Format format f).
  Proof.
    intros ** ? **.
    destruct H as [witness [Hcompute Hcorrect]].
    eapply Hresi in Hcompute as [res Hcompute].
    
    do 2 eexists.
    split; eauto.
  Qed.
  Lemma list_env_resilient:
    forall A Q (monoid: Monoid Q) (format1: FormatM A Q)
      (Henv_resilient: env_resilient format1),
      env_resilient (format_list format1).
  Proof.
    unfold env_resilient.
    intros * Henv_in.
    induction x.
    - simpl. econstructor.
      apply ReturnComputes.
    - simpl; intros.
      repeat destruct_bind.

      eapply (Henv_in _ _ env2) in H; destruct_ex.
      eapply (IHx _ (snd x2)) in H0; destruct_ex.
      
      econstructor.
      repeat eapply BindComputes; eauto.
  Qed.
  
  Lemma IndexedSumType_resilience:
    forall n m (types: Vector.t Type n)
      (formats : ilist (B:= fun T => FormatM T ByteString) types),
    forall fin_format
      (Hfin_resi: env_resilient fin_format) 
      (Hfroms_resi: forall idx, env_resilient (ith formats idx)), 
      env_resilient (format_IndexedSumType m types formats fin_format).
  Proof.
    Transparent format_IndexedSumType.
    unfold format_IndexedSumType.
    unfold env_resilient.
    intros n m typs **.
    repeat destruct_bind.
    
    (* Process the fin_type*)
    eapply Projection_resilience in H as [idx H]; auto.
    
    (*Process sumtype*)
    eapply SumType_resilience in H0 as [res H0]; auto.
    
    eexists.
    repeat eapply BindComputes; eauto.
  Qed.
  
  (* This lemma shows that resiliance is stronger than the
        precondition for correct lists decoders
   *)
  Lemma resiliance_maintained:
    forall A (format_A: FormatM A ByteString) encode_A
      (encode_A_OK : CorrectAlignedEncoder format_A encode_A),
      env_resilient format_A ->
      forall (a : A) (l : list A) (env : CacheFormat)
        (tenv' tenv'' : ByteString * CacheFormat),
        format_A a env ∋ tenv' ->
        format_list format_A l (snd tenv') ∋ tenv'' ->
        exists tenv3 tenv4 : ByteString * CacheFormat,
          projT1 encode_A_OK a env = Some tenv3 /\
            format_list format_A l (snd tenv3) ∋ tenv4.
  Proof.
    intros.
    destruct encode_A_OK.
    simpl in *.
    split_and.
    destruct (x a env) eqn:HH; cycle 1.
    { (* impossible case *)
      eapply H6 in HH. exfalso; apply HH; eauto. }

    eapply list_env_resilient in H1 as []; auto.
    do 2 eexists; split; eauto.
  Qed.
  (*Not needed for now.*)
  Lemma format_list_permutation':
    forall (A : Type) (format1 : FormatM A ByteString) (s ls' : list A)
      (Henv_resilient: env_resilient format1),
      Permutation s ls' ->
      env_resilient (format_list format1).
  Abort.

  (* Lemma about how resilience implies formats can be permuted!

     Notice the conclusion is not an instance of `env_resilient_not`
     because it talks about two different lists! *)
  Lemma format_list_permutation:
    forall (A : Type) (format1 : FormatM A ByteString) (ls ls' : list A)
      (Henv_resilient: env_resilient format1),
      Permutation ls ls' ->
      forall (env : CacheFormat),
        (forall v0 : ByteString * CacheFormat, format_list format1 ls env ∌ v0) ->
        forall v : ByteString * CacheFormat, format_list format1 ls' env ∌ v.
  Proof.
    intros * Henv_in Hperm .
    induction Hperm; try clear Hperm.
    + intros * HH.
      eapply HH.
    + intros ** ? **.
      simpl in *.
      repeat destruct_bind.

      eapply IHHperm; eauto.
      intros * ?.
      eapply H.
      repeat eapply BindComputes; eauto.
      
    + intros * HH * HH0.
      
      simpl in HH0.
      repeat destruct_bind.

      eapply (Henv_in _ _ env) in H0; destruct_ex.
      eapply (Henv_in _ _ (snd x4)) in H; destruct_ex.
      eapply list_env_resilient in H2; destruct_ex; auto.

      
      eapply HH; clear HH.
      simpl.
      repeat eapply BindComputes; eauto.
    + intros * HH * HH0.
      eapply IHHperm2; eauto.
  Qed.
End Resilience.

Section Permutation.

  (* Since identity is a permutation, composing with permutations
  refines to no composition*)
  Lemma refine_compose_permutation:
    forall A T s env (format1: FormatM (list A) T),
      refine (Compose_Format (format1) (Permutation (A:=A)) s env)
             (format1 s env).
  Proof.
    unfold refine; intros *; repeat rewrite unfold_computes.
    unfold Compose_Format.
    exists s; split ; auto.
  Qed.


  
  (** *The Format*)
  
  (* | Adds a type to the type of a SumType. Doesn't change the element.
     Has no computational effect.
   *)
  Definition lift_SumType (A:Type) {n:nat} {types:Vector.t Type n} :
    SumType types -> SumType (Vector.cons Type A _ types):=
    match types as typs return
          SumType typs -> SumType (Vector.cons Type A _ typs) with
    | Vector.nil =>
        (* Impossible case: with an empty vector can't construct the SumType*)
        fun elem => let X1 := match elem return A with
                           end in X1
    | Vector.cons a n typs' =>
        fun elem => inr elem
    end.

  (* Turns any element into a list, given projections for all it's
  components*)
  Fixpoint to_list {n:nat} {S:Type} {types:Vector.t Type n}:
    forall projections: ilist (B:= fun T => S -> T) types, 
      S -> list (SumType types):=
    match types as typs return
          ilist (B:= fun T => S -> T) typs ->  
          S -> list (SumType typs) with
    | Vector.nil => fun _ _ => Datatypes.nil
    | @Vector.cons _ a n' typs' =>
        let typs:= Vector.cons Type a n' typs' in
        fun projs S =>
          (inj_SumType typs Fin.F1 (prim_fst projs S))
            :: map (lift_SumType a) (to_list (prim_snd projs) S)
    end.

  (* Format for lists of SumTypes. *)
  Definition SumType_list_Format
             (m : nat) (types : Vector.t Type m)
             (fin_format: FormatM (Fin.t m) ByteString)
             (formats: ilist (B:= fun T => FormatM T ByteString) types):
    FormatM (list (SumType types)) ByteString:=
    format_list (format_IndexedSumType m types formats fin_format).
  
  
  (* Permutation Formats, from lists. *)
  Definition permutation_list_Format
             (m : nat) (types : Vector.t Type m)
             (fin_format: FormatM (Fin.t m) ByteString)
             (formats: ilist (B:= fun T => FormatM T ByteString) types):
    FormatM (list (SumType types)) ByteString:=
    Compose_Format (SumType_list_Format m types fin_format formats)
                   (Permutation (A:=SumType types)).
  
  Definition permutation_Format
             S (m : nat) (types : Vector.t Type m)
             (projections: ilist (B:= fun T => S -> T) types)
             (fin_format: FormatM (Fin.t m) ByteString)
             (formats: ilist (B:= fun T => FormatM T ByteString) types):
    FormatM S ByteString:=
    permutation_list_Format m types fin_format formats ◦ to_list projections.

  
  (** *The Encoder*)

  Definition Permutation_encoder {n} {types: Vector.t Type n}
             (S:Type)
             (projs: ilist (B:= fun T : Type => S -> T) types)
             (encode_fin:   forall sz0 : nat, AlignedEncodeM sz0)
             (encoders: ilist (B:= fun T => forall sz, @AlignedEncodeM _ T sz) types)
    : forall n : nat, AlignedEncodeM n:=
    Projection_AlignedEncodeM
      (AlignedEncodeList (encoder_IndexedSumType encode_fin encoders))
      (to_list projs).
    
  Lemma Permutation_Encoder_Correct:
    forall S m types projs fin_format formats
      (encode_fin:   forall sz0 : nat, AlignedEncodeM sz0)
      (encoders: ilist (B:= fun T => forall sz, @AlignedEncodeM _ T sz) types),
    forall (Hfin_resi: env_resilient fin_format)
      (Hformats_resi: IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                        (fun idx : Fin.t m => env_resilient (ith formats idx)))
      (Hcorrect_fin: CorrectAlignedEncoder fin_format encode_fin)
      (Hcorrect_encoders: IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                            (fun idx : Fin.t m => CorrectAlignedEncoder (ith formats idx) (ith encoders idx))),
      CorrectAlignedEncoder (@permutation_Format S m types projs fin_format formats)
                            (Permutation_encoder S projs encode_fin encoders).
  Proof.
    intros.
    pose proof (IterateBoundedIndex.Lookup_Iterate_Dep_Type _ Hformats_resi); clear Hformats_resi.
    
    unfold permutation_Format, permutation_list_Format, SumType_list_Format.
    eapply CorrectAlignedEncoderProjection.
    eapply refine_CorrectAlignedEncoder; try split.
    - eapply refine_compose_permutation.
    - intros HH0 ? HH1.
      rewrite unfold_computes in HH1.
      destruct HH1 as [ls' [HH Hperm]].
      eapply format_list_permutation; cycle 1 (*whitout this order, a different assumption triggers*)
      ; try eassumption; [ (*assert one goal left*) ].
      clear HH Hperm.
      eapply IndexedSumType_resilience; eauto.
    - unshelve eapply CorrectAlignedEncoderForFormatList; cycle 1.
      + eapply resiliance_maintained.
        eapply IndexedSumType_resilience; auto.
      + apply IndexedSumType_Encoder_Correct; assumption.
  Qed.
    
        
End Permutation.

Global Arguments permutation_Format {S m types} projections fin_format formats. 
Global Opaque permutation_Format.


Create HintDb resilience.
Global Hint Resolve word_resilience: resilience.
Global Hint Resolve format_enum_resilience: resilience.
