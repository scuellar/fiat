Set Nested Proofs Allowed.
(** *The formats here are derived using automation.
    We can still add them to automation using the appropriate hooks.
 *)

Require Import 
  Fiat.Narcissus.Common.Notations
  Fiat.Narcissus.Common.Specs
  Fiat.Narcissus.Common.EquivFormat
  Fiat.Narcissus.Common.ComposeOpt
  Fiat.Narcissus.Common.ParametricSort
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
  Fiat.Narcissus.BinLib.AlignedDecodeMonad
  Fiat.Narcissus.BinLib.AlignedDecoders.

(* Automation *)
Require Import
  Fiat.Narcissus.Automation.NormalizeFormats
  Fiat.Narcissus.Automation.ExtractData
  Fiat.Narcissus.Automation.Common
  Fiat.Narcissus.Automation.Invertible.

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
     it fail. They either succeeds for all environmnets or fails for
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


Section List2Ilist.
  (* In this section we construct the functions to go from ilist to
    list and back. The key functions are:

    * `ito_list`: Maps an heterogeneous list into a homogeneous list
       of SumTypes. Specifically, it maps `ilist(B:=id) types` to a
       `list (SumType types)`.

    * `ifrom_list`: Maps a homogeneous list of SumTypes back into the
      heterogeneous list, failing if the elements are not all there in
      the right order. Specifically, it maps `list (SumType types)`
      into a `option (ilist(B:=id) types)`.

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

  (** *ito_list*)
  (** Maps an heterogeneous list into a homogeneous list of
  SumTypes. Specifically, it maps `ilist(B:=id) types` to a `list
  (SumType types)`. *)
  Fixpoint ito_list {n:nat} {types:Vector.t Type n}:
    ilist (B:=id) types -> list (SumType types):=
    match types as typs return
          ilist (B:=id) typs ->
          list (SumType typs) with
    | Vector.nil => constant Datatypes.nil
    | @Vector.cons _ a n' typs' =>
        let typs:= Vector.cons Type a n' typs' in
        fun ils =>
          (inj_SumType typs Fin.F1 (prim_fst ils))
            :: map (lift_SumType a) (ito_list (prim_snd ils))
    end.

  (** *ifrom_list*)
  (** Maps a homogeneous list of SumTypes back into the
      heterogeneous list, failing if the elements are not all there in
      the right order. Specifically, it maps `list (SumType types)`
      into a `option (ilist(B:=id) types)`. *)

  (*We use some definitions/notation to make the function readable
    NOTE: These definitions should be global and the notation should
    be generic over a typeclass for Monads. However Narcissus alrady
    defines many of these notations in a weaker way so we are stuck
    doing this local notation where necessary.  *)
  Definition DecodeBindOpt'
             {A B C}
             (a : option (A * B))
             (k : A -> B -> option C)
    : option C :=
    BindOpt a (fun a => let (a, b) := a in k a b).
  Bind Scope option_scope with option.
  Declare Scope option_scope.
  Delimit Scope option_scope with opt.
  Open Scope option_scope.
  Notation "x <- y ; z" := (BindOpt y (fun x => z))
                             (at level 81, right associativity,
                               format "'[v' x  <-  y ; '/' z ']'") : option_scope.
  Notation "`( a , b ) <- c ; k" :=
    (DecodeBindOpt' c (fun a b => k)) : option_scope.

  (* gets the head and tail of a list, if any, otherwise returns None. *)
  Definition getCons {A} (ls:list A): option (A * list A):=
    match ls with
    | [] => None 
    | hd::tl => Some (hd,tl)
    end.

  Definition dropSumType {n : nat} {types : Vector.t Type n} {A:Type}:
    SumType (Vector.cons Type A n types) -> option (SumType types):=
    match
      types as t in (Vector.t _ n)
      return (SumType (Vector.cons Type A n t) -> option (SumType t))
    with
    | @Vector.nil _ => constant None
    | @Vector.cons _ h n types0 =>
        fun elem0 : SumType _ => match elem0 with
                              | inl _ => None
                              | inr elem1 => Some elem1
                              end
    end.

  
  (* Add a SumType to the head of an ilist, if and only if it has the right type (i.e. the first type) *)
  Definition ilist_cons {n:nat} {types:Vector.t Type n} {t0}
    (el: SumType (Vector.cons Type t0 n types)) (ils: ilist types) :
    option (ilist (Vector.cons Type t0 n types)) :=
    match
      types as t in (Vector.t _ n1)
      return
      (SumType (Vector.cons Type t0 n1 t) ->
       ilist t -> option (ilist (Vector.cons Type t0 n1 t)))
    with
    | @Vector.nil _ =>
        (* Type list is empty, so the element is necessarily the first
        one (i.e. `t0`) *)
        fun el ils => Some {| prim_fst := el; prim_snd := ils |}
    | @Vector.cons _ t1 n1 types1 =>
        (* The typelist is not empty, we need to check that the
        element is of type `t0`. We just need to check it's
        constructor is `inl` *)
        fun el ils => match el with
                   | inl firstType =>
                       Some {| prim_fst := firstType; prim_snd := ils |}
                   | inr _ => None
                   end
    end el ils.
  
  (* Like `traverse`, specialized to `list`s and `option` *)
  Fixpoint traverseOp {a b: Type} (f: a -> option b) (ls: list a): option (list b):=
    match ls with
      [] => Some []
    | hd::tl => match (f hd, traverseOp f tl) with
              | (None, _) => None
              | (_, None) => None
              | (Some hd', Some tl') => Some (hd' :: tl')
              end
    end.

  (* Take a list of `SumType`s and remove the frist type
            from the vector, if the list doesn't contain anything of
            that type. Otherwise, return None.*)
  Definition dropListSumType {n : nat} {types : Vector.t Type n} {A:Type}:
    list (SumType (Vector.cons _ A n types)) -> option (list (SumType types)):=
    traverseOp dropSumType.
  
  Fixpoint ifrom_list {n:nat} {types:Vector.t Type n}
    {struct types}: list (SumType types) -> option (ilist (B:=id) types):=
    match
      types as t in (Vector.t _ n0)
      return (list (SumType t) -> option (ilist t))
    with
    | @Vector.nil _ =>
        fun ls0 => match ls0 with
                | [] => Some ()
                | s :: _ => let H := match s return (option ()) with
                                   end in H
                end
    | @Vector.cons _ h n0 types0 =>
        fun ls0 =>
          (* Make sure the list has another element*)
          `(s, ls1) <- getCons ls0;
  (* Drop the types of the tail to call `ifrom_list` recursively*)
  ls3 <- dropListSumType ls1;
  ls5 <- @ifrom_list n0 types0 ls3;
  (* Append the new head to the `ilist` *)
  ilist_cons s ls5
  end.
  Close Scope option_scope.


  (* #Inverses: These two functions are inverses of each other. *)
  
  Lemma ifrom_ito_list:
    forall {n : nat}
      {types : Vector.t Type n}
      (ls : list (SumType types))
      (ils : ilist types),
      ifrom_list ls = Some ils ->
      ito_list ils = ls.
  Proof.
  Admitted.
  
  Lemma ito_ifrom_list:
    forall {n : nat}
      {types : Vector.t Type n}
      (ils : ilist types),
      ifrom_list (ito_list ils) = Some ils.
  Proof.
  Admitted.
  
End List2Ilist.


Section SortIlist.
  (* This section defines the functions to sort `list (SumType types)`
   and `ilist`s and proves the approriate properties about them and
   their relationships.  The key definitions are:

   * `SumTypeSort` a function that orders lists of SumType's, based on
     the index of the sumtype.

   * `sortToIlist` that translates a list of SumTypes, to an ilist, by
     first ordering it.

   *)

  (** + `SumTypeSort` a function that orders lists of SumType's, based on the index of the sumtype. *)

  (* | SumTypeLt : Less than for `SumType`'s *)
  Definition finTLe {n} (ft1 ft2 : Fin.t n): bool:=
    nat_leb (f2n ft1) (f2n ft2).
  Definition SumTypeLt {m : nat} {types : Vector.t Type m} (s1 s2 : SumType types): bool :=
    finTLe (SumType_index _ s1) (SumType_index _ s2).
  Lemma SumTypeLt_inl_inr:
    forall {n : nat}
      {types : Vector.t Type n},
    forall A1 A2  x y,
      @SumTypeLt _ (Vector.cons _ A1 _ (Vector.cons _ A2 _ types)) (inl x) (inr y).
  Proof. constructor. Qed.
  
  Lemma SumTypeLt_inr_inl:
    forall {n : nat}
      {types : Vector.t Type n},
    forall A1 A2  x y,
      ~ @SumTypeLt _ (Vector.cons _ A1 _ (Vector.cons _ A2 _ types)) (inr y) (inl x).
  Proof.
    intros ** ?. inversion H.
    unfold SumTypeLt, finTLe, SumType_index in H1.
    rewrite <- f2n_FS in H1; inversion H1.
  Qed.
  Lemma SumTypeLt_lift:
    forall h {n : nat}
      {types : Vector.t Type n},
    forall (x y : SumType types),
      SumTypeLt (lift_SumType h x) (lift_SumType h y) =
        SumTypeLt x y.
  Proof.
    destruct types.
    - simpl. destruct x.
    - simpl.
      induction types; simpl.
      + intros. unfold SumType in *; reflexivity.
      + intros. 
        unfold SumTypeLt; simpl.
        unfold SumType_index.
        Lemma finTLe_FS:
          forall n (x y:Fin.t n), finTLe (Fin.FS x) (Fin.FS y) = finTLe x y.
        Proof.
          intros.
          unfold finTLe, f2n, proj1_sig; simpl.
          destruct (Fin.to_nat x); destruct (Fin.to_nat y); reflexivity.
        Qed.
        eapply finTLe_FS.
  Qed.
  
  Lemma SumTypeLt_lift':
    forall h {n : nat}
      {types : Vector.t Type n},
      (fun x y => is_true (SumTypeLt (lift_SumType h x) (lift_SumType h y))) =
        (fun x y => SumTypeLt(types:=types) x y).
  Proof.
    intros. extensionality x; extensionality y.
    rewrite SumTypeLt_lift; reflexivity.
  Qed.
  
  Definition SumTypeSort {m : nat} {types : Vector.t Type m} := sort (@SumTypeLt m types).

  (** + SortToIlist: a function to reorder lists of sumtypes! *)
  (* | Reorders a list, and turns it back into an ilist. This
         function might fail if the input does not have all the
         entries (as determined by `types`) or has repeated elements.

         This version uses MergeSort which is O(n log n). However, it
         still uses `ifrom_list` which is unfortunately O(n^2).  *) 

  Definition sortToIlist {m : nat} {types : Vector.t Type m}
    (ls : list (SumType types)): option (ilist(B:=id) types):=
    ifrom_list (SumTypeSort ls). 

  (** + Properties of sorting. *)

  Lemma Permutation_SumTypeSort:
    forall {n : nat}
      {types : Vector.t Type n}
      (ls : list (SumType types)),
      Permutation (SumTypeSort ls) ls.
  Proof. symmetry; eapply Permuted_sort. Qed.

  (* | All elements in a list, produced by `ito_list`, are different
     as given SumType constructors*)
  Inductive allDifferent {A} (R: relation A): list A -> Prop :=
  | AllFidNil: allDifferent R []%list
  | AllFidCons: forall a ls, allDifferent R ls
                        -> Forall (fun b=> ~ (R a b) \/ ~ (R b a)) ls
                        -> allDifferent R (a::ls).
  
  Lemma allDifferent_map:
    forall A B (R:relation B) (f: A -> B) ls,
      allDifferent (fun x y => R (f x) (f y)) ls ->
      allDifferent R (map f ls).
  Proof.
  Admitted.
  Lemma StronglySorted_map:
    forall A B (R:relation B) (f: A -> B) ls,
      Sorted.StronglySorted (fun x y => R (f x) (f y)) ls ->
      Sorted.StronglySorted R (map f ls).
  Proof.
  Admitted.

  Lemma Permutation_Sorted_eq:
    forall A (R: relation A) (ls1 ls2 : list A)
      (* (Hantisym: antisymmetric _ R) *)
      (HallDiff: allDifferent R ls1),
      Permutation ls1 ls2 ->
      Sorting.Sorted.StronglySorted R ls1 ->
      Sorting.Sorted.StronglySorted R ls2 ->
      ls1 = ls2.
  Proof.
    induction ls1 as [| a tl1].
    - intros. apply Permutation_nil in H; subst; reflexivity.
    - intros.
      (* a is in ls2. *)
      eapply Permutation_in in H as HIn2; [ |left; reflexivity].
      (* a is smaller than all others. *)
      inversion H0; subst; clear H0.
      (* a must be the head of ls2 *)
      destruct ls2 as [|a' tl2]; [ inversion HIn2|]. 

      inversion HIn2.
      + (*a = a' *)  subst. f_equal; eapply IHtl1; try eassumption.
        * inversion HallDiff; auto.
        * eapply Permutation_cons_inv; eassumption.
        * inversion H1; eassumption.
      + (* In a tl2, so a' can't be in ls1!*)
        inversion H1; subst.
        symmetry in H;
          eapply Permutation_in in H as HIn1; [ |left; reflexivity].
        destruct HIn1.
        * subst. f_equal; eapply IHtl1; try eassumption.
          -- inversion HallDiff; auto.
          -- symmetry; eapply Permutation_cons_inv; eassumption.
        * exfalso.
          inversion HallDiff; subst.
          eapply Forall_forall1_transparent in H10.
          2: eapply H2.
          destruct H10 as [HH|HH]; apply HH.
          -- eapply Forall_forall1_transparent in H5; eauto.
          -- eapply Forall_forall1_transparent in H7; eauto.
  Qed.
  
  Lemma ito_list_allDifferent:
    forall {n : nat}
      {types : Vector.t Type n}
      (ils : ilist types),
      allDifferent (SumTypeLt(types:=types))  (ito_list ils).
  Proof.
    induction types.
    - simpl. intros; constructor.
    - intros. destruct ils.
      destruct types eqn:HH.
      + do 2 constructor.
      + constructor.
        * eapply allDifferent_map.
          rewrite SumTypeLt_lift'.
          eapply IHtypes.
        *  simpl.
           match goal with
             |- Forall ?P ?X =>
               remember P as p
           end.
           constructor.
           -- subst p.
              right. eapply SumTypeLt_inr_inl.
           -- match goal with
                |- Forall ?p (map ?f1 ?ls) =>
                  remember p as P; remember ls as LS
              end.
              clear - Heqp.
              induction LS.
              ++ constructor.
              ++ constructor. 
                 ** subst P; right. apply SumTypeLt_inr_inl.
                 ** eapply IHLS.
  Qed.

  Lemma ito_list_Sorted:
    forall {n : nat}
      {types : Vector.t Type n}
      (ils : ilist types),
      Sorted.StronglySorted (SumTypeLt(types:=types))
        (ito_list ils).
  Proof.
    (* Proof is similar to `ito_list_allDifferent` modularize?*)
    induction types.
    - simpl. intros; constructor.
    - intros. destruct ils.
      destruct types eqn:HH.
      + do 2 constructor.
      + constructor.
        * eapply StronglySorted_map.
          rewrite SumTypeLt_lift'.
          eapply IHtypes.
        * simpl.
          match goal with
            |- Forall ?P ?X =>
              remember P as p
          end.
          constructor.
          -- subst p.
             eapply SumTypeLt_inl_inr.
          -- match goal with
               |- Forall ?p (map ?f1 ?ls) =>
                 remember p as P; remember ls as LS
             end.
             clear - Heqp.
             induction LS.
             ++ constructor.
             ++ constructor. 
                ** subst P. apply SumTypeLt_inl_inr.
                ** eapply IHLS.
  Qed.

  Lemma total_SumTypeLt:
    forall {n : nat}
      {types : Vector.t Type n},
    forall x y : SumType types, SumTypeLt x y = true \/ SumTypeLt y x = true.
  Proof.
    intros.
    unfold SumTypeLt.
    unfold finTLe.
    Definition total_nat_leb: forall n1 n2,
        nat_leb n1 n2 \/ nat_leb n2 n1.
    Proof. induction n1; destruct n2; eauto. Qed.
    eapply total_nat_leb.
  Qed.
  Lemma Transitive_nat_leb: Transitive nat_leb.
  Proof.
    intros n1;
      induction n1.
    - intros n2; destruct n2; eauto.
    - intros n2; destruct n2; eauto.
      + simpl; intros; congruence.
      + simpl; intros n3; destruct n3; eauto.
  Qed.
  Lemma Transitive_SumTypeLt: 
    forall {n : nat}
      {types : Vector.t Type n},
      Transitive (@SumTypeLt _ types).

    unfold Transitive.
    unfold SumTypeLt, finTLe.
    intros ?????.
    eapply Transitive_nat_leb.
  Qed. 
  Lemma SumTypeSort_Permutation:
    forall {n : nat}
      {types : Vector.t Type n}
      (ls : list (SumType types))
      (ils : ilist types),
      Permutation (ito_list ils) ls ->
      SumTypeSort ls = ito_list ils.
  Proof.
    unfold SumTypeSort.
    intros.
    symmetry; eapply Permutation_Sorted_eq; eauto.
    - eapply ito_list_allDifferent.
    - etransitivity; try eassumption.
      eapply Permuted_sort.
    - eapply ito_list_Sorted.
    - eapply @StronglySorted_sort.
      + apply total_SumTypeLt.
      + apply Transitive_SumTypeLt.
  Qed.
  Lemma sortToIlist_Permutation_inverse:
    forall {n : nat}
      {types : Vector.t Type n}
      (ls : list (SumType types))
      (ils : ilist types),
      Permutation (ito_list ils) ls ->
      sortToIlist ls = Some ils.
  Proof.
    unfold sortToIlist. intros.
    rewrite <- ito_ifrom_list.
    erewrite SumTypeSort_Permutation; eauto.
  Qed.
  Lemma Permutation_sortToIlist_inverse:
    forall {n : nat}
      {types : Vector.t Type n}
      (ls : list (SumType types))
      (ils : ilist types),
      sortToIlist ls = Some ils -> Permutation (ito_list ils) ls.
  Proof.
    unfold sortToIlist.
    intros.
    etransitivity; cycle 1.
    - apply Permutation_SumTypeSort.
    - unfold SumTypeSort in *.
      remember (sort SumTypeLt ls) as sorted_ls.
      erewrite ifrom_ito_list; eauto.
  Qed.
  
End SortIlist.

Section SortDecodeCorrect.
  (* Last section defined `sort_filter` to sort `lists` into
     `ilist`. This section proves that `sort_filter` is a correct
     decoder for the `empty_format`, that sorts a `list (SumType
     types)` (existing in the context) and translates it into an
     ilist.

     The key difficulty in proving the lemma
     `sort_list_SumType_Correct_Decoder`, at the end of the section,
     is to take into account the failure in decoding. *)

  (* We generalize the notion of `decides` to include the possibility
     of failure.  While decides has type

    ``` decides : bool -> Prop -> Prop ```

    We define a new predicate that has type

    ``` decidesOpt : option a -> (a -> Prop) -> Prop ```

    Which encodes the fact that, if decoding went wrong, then it
    was impossible to satisfy the predicate in the first place.

   *)
  Definition decidesOpt {a} (op: option a) (predicate: a -> Prop):=
    Ifopt op as s Then predicate s Else forall s, ~ predicate s.
  
  Definition decidesOptBool {a} (op: option a) (b: a -> bool) (predicate: a -> Prop):=
    Ifopt op as s Then (General.decides (b s) (predicate s)) Else forall s, ~ predicate s.
  

  Definition filter_decode {S B} (op:option S): DecodeM (S * B) B:=
    (fun t' ctxD => Ifopt op as s Then Some (s, t', ctxD) Else None).
  Definition sort_filter {m} {types : Vector.t Type m} (v : list (SumType types)):
    DecodeM ((ilist(B:=id) types) * ByteString)  ByteString:= (filter_decode (sortToIlist v)).

  Corollary CorrectDecoderEmptyOpt {S T}
    : forall (monoid : Monoid T)
             (Source_Predicate : S -> Prop)
             (decode_inv : CacheDecode -> Prop)
             (op : option S),
      (forall s', Ifopt op as s Then Source_Predicate s' -> s' = s Else True) ->
      decidesOpt op Source_Predicate 
      -> CorrectDecoder
           monoid
           Source_Predicate
           Source_Predicate
           eq
           empty_Format
           (filter_decode op)
           decode_inv
           empty_Format.
  Proof.
    intros.
    destruct op.
    - eapply ExtractViewFrom; eauto; unfold empty_Format; eauto.
    - Transparent CorrectDecoder.
      unfold CorrectDecoder, empty_Format; split. intros.
      + elimtype False; eapply H0. eauto.
      + discriminate.
  Qed.

  


  Definition bothOpt {A: Type} (opt:option A) (b: A -> bool): option A:=
    (match opt with
     | Some s => if b s then Some s else None
     | None   => None 
     end).

  (** *sort_list_SumType_Correct_Decoder*)
  (* This decoder for the `empty_Format` can untangle a permuted
     list and lift it back into an ordered ilist.

     That is, map a `list (SumType types)` to an `ilist(B:=id) types`,
     with possibility of failure if the initial list can't be strictly
     ordered in the desired ilist, of the given length, without
     repetition. *)

  Lemma sort_list_SumType_Correct_Decoder:
    forall n (types: Vector.t Type n) cache_inv v1,
      CorrectDecoder ByteStringQueueMonoid (fun ils : ilist types => Permutation (ito_list ils) v1)
        (fun ils : ilist types => Permutation (ito_list ils) v1) eq empty_Format 
        (sort_filter v1) cache_inv empty_Format.
  Proof.
    intros.
    eapply CorrectDecoderEmptyOpt; cycle 1.
    - intros. 
      destruct (sortToIlist v1) eqn:HSTv1; simpl.
      + apply Permutation_sortToIlist_inverse; assumption.
      + intros ** ?.
        eapply sortToIlist_Permutation_inverse in H.
        rewrite H in HSTv1; discriminate.
    - destruct (sortToIlist v1) eqn:HSTv1; simpl; try tauto.
      intros.
      eapply sortToIlist_Permutation_inverse in H.
      rewrite H in HSTv1. inversion HSTv1; reflexivity.
  Qed.

End SortDecodeCorrect.




Section ListPermutations.
  (* This section defines formats for permutations of ilist.
     Specifically, we create a format for `ilist(B:=id) types` that:
     - Translates to `list (SumType types)`
     - Permutes the list with `Permutation`
     - Then formats each element in the permuted, heterogeneous list.
   *)


  (* Pramble *)
  (* Lemma for normalization. Projections and composition can be merged. *)
  Lemma EquivFormat_compose_projection {T S S' S''}
    (format_S'' : FormatM S'' T)
    (f : S -> S')
    (r : S' -> S'' -> Prop)
    : EquivFormat (Projection_Format (Compose_Format format_S'' r) f)
        (Compose_Format format_S'' (fun a b => r (f a) b)).
  Proof.
    unfold EquivFormat, refineEquiv, Projection_Format, Compose_Format, compose, Bind2; split;
      intros ? ?.
    - rewrite unfold_computes in *.
      destruct_ex; split_and; eexists.
      rewrite unfold_computes;  eauto.
    - rewrite unfold_computes in *.
      destruct_ex; split_and.
      rewrite unfold_computes in H0.
      destruct_ex; split_and.
      eexists; intuition eauto.
      subst; eauto.
  Qed.
  
  Ltac normalize_step BitStringT ::=
    (first
       [ match goal with
         | |- EquivFormat ?z ?x => is_evar z; apply EquivFormat_reflexive
         end; idtac "1"
       | eapply EquivFormat_trans; [ apply sequence_assoc |  ]
         ; idtac "3"
       | eapply EquivFormat_trans;
         [ apply sequence_mempty with (monoid := BitStringT) |  ]
         ; idtac "5"
       | eapply EquivFormat_ComposeIf; intros
         ; idtac "6"
       | eapply EquivFormat_trans;
         [ apply EquivFormat_If_Then_Else with (monoid := BitStringT) |  ]
         ; idtac "8"
       | apply EquivFormat_If_Then_Else_Proper
         ; idtac "9"
       | eapply EquivFormat_UnderSequence';
         [ repeat
             (eapply EquivFormat_trans;
              [ first [eapply EquivFormat_compose_map; idtac "10.0" |
                        eapply EquivFormat_compose_projection; idtac "10.1" ] |  ] );
           apply EquivFormat_reflexive
         |  ] ; idtac "10"
       | eapply EquivFormat_Projection_Format_Empty_Format';
         [ repeat eapply EquivFormat_compose_map;
           apply EquivFormat_reflexive ] ; idtac "11"
       | unfold EquivFormat; intros; reflexivity ]); 
    intros.
  
  (** *The Format*)
  
  (* | Adds a type to the type of a SumType. Doesn't change the element.
     Has no computational effect.
   *)
  
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
  
  Definition permutation_ilist_Format
    (m : nat) (types : Vector.t Type m)
    (fin_format: FormatM (Fin.t m) ByteString)
    (formats: ilist (B:= fun T => FormatM T ByteString) types):
    FormatM (ilist types) ByteString:=
    permutation_list_Format m types fin_format formats ◦ ito_list.

  (** *The Encoder*)

  Definition Permutation_ilist_encoder {n} {types: Vector.t Type n}
    (encode_fin:   forall sz0 : nat, AlignedEncodeM sz0)
    (encoders: ilist (B:= fun T => forall sz, @AlignedEncodeM _ T sz) types)
    : forall n : nat, AlignedEncodeM n:=
    Projection_AlignedEncodeM
      (AlignedEncodeList (encoder_IndexedSumType encode_fin encoders))
      ito_list.

  
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
  
  Lemma Permutation_ilist_Encoder_Correct:
    forall m types fin_format formats
           (encode_fin:   forall sz0 : nat, AlignedEncodeM sz0)
           (encoders: ilist (B:= fun T => forall sz, @AlignedEncodeM _ T sz) types),
    forall (Hfin_resi: env_resilient fin_format)
           (Hformats_resi: IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                             (fun idx : Fin.t m => env_resilient (ith formats idx)))
           (Hcorrect_fin: CorrectAlignedEncoder fin_format encode_fin)
           (Hcorrect_encoders: IterateBoundedIndex.Iterate_Dep_Type_BoundedIndex
                                 (fun idx : Fin.t m => CorrectAlignedEncoder (ith formats idx) (ith encoders idx))),
      CorrectAlignedEncoder (@permutation_ilist_Format m types fin_format formats)
        (Permutation_ilist_encoder encode_fin encoders).
  Proof.
    intros.
    pose proof (IterateBoundedIndex.Lookup_Iterate_Dep_Type _ Hformats_resi); clear Hformats_resi.
    
    unfold permutation_ilist_Format, permutation_list_Format, SumType_list_Format.
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
  
  (** *The Decoder*)
  Lemma ito_list_length:
    forall n (types: Vector.t Type n) (ils: ilist types) ,
      (| ito_list ils |) = n.
  Proof.
    intros ??; induction types.
    - intros. reflexivity.
    - intros. simpl.
      f_equal; rewrite map_length.
      eapply IHtypes.
  Qed.
  
  (* This simple decoder, simply reads a list of sumtypes, then passes
     that into a second decoder to extract the ilist.  The second
     decoder shouldn't consume any characters and, in practice, it
     will decode the empty format. However, these facts are not enforced.
   *)
  Definition permutation_ilist_decoder
    {m}
    {types : Vector.t Type m}
    (fin_decoder : ByteString ->
                   CacheDecode ->
                   option (Fin.t m * ByteString * CacheDecode))
    (decoders : ilist
                  (B:= fun T : Type => @DecodeM (T * ByteString) ByteString
                                         EmptyStore.test_cache) types)
    (decode2 : list (SumType types) ->
               DecodeM ((ilist(B:=id) types) * ByteString) ByteString):
    DecodeM (ilist types * ByteString) ByteString
    :=
    (sequence_Decode
       (decode_list (decoder_IndexedSumType fin_decoder decoders)
          m) decode2).


  
  (* Easier to proof version.
  The better version to automate below
   *)
  Lemma Permutation_ilist_decoder_correct': 
    forall m (types: Vector.t Type m) cache_inv
           (cache_invariants: Vector.t ((_ -> Prop) -> Prop) m) fin_cache_inv
           (fin_format : FormatM (Fin.t m) ByteString)
           fin_decoder view_fin
           (fin_correct: cache_inv_Property cache_inv fin_cache_inv ->
                         CorrectDecoder ByteStringQueueMonoid view_fin 
                           view_fin eq fin_format fin_decoder cache_inv fin_format)
           (formats : ilist types)
           (invariants: ilist (B:= fun T : Type => T -> Prop) types)
             (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
             (formatrs_decoders_correct : IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                                            (fun idx =>
                                               cache_inv_Property cache_inv (Vector.nth cache_invariants idx)
                                               -> CorrectDecoder
                                                    ByteStringQueueMonoid
                                                    (ith invariants idx)
                                                    (ith invariants idx)
                                                    eq
                                                    (ith formats idx)
                                                    (ith decoders idx)
                                                    cache_inv
                                                    (ith formats idx)))
             (Hinvariants_ok: forall (ils : ilist(B:=id) types) (v : list (SumType types)),
                 Permutation (ito_list ils) v ->
                 forall x : SumType types,
                   In x (ito_list ils) ->
                   view_fin (SumType_index types x) /\
                     ith invariants (SumType_index types x) (SumType_proj types x))
             (P_inv2:(CacheDecode -> Prop) -> Prop)
             (Hcache_inv2: cache_inv_Property cache_inv
                             (fun P : CacheDecode -> Prop =>
                                (fin_cache_inv P /\
                                   IterateBoundedIndex.Iterate_Ensemble_BoundedIndex'
                                     (fun idx : Fin.t m => Vector.nth cache_invariants idx P)) /\
                                  P_inv2 P)),
        CorrectDecoder ByteStringQueueMonoid
          (constant True) (constant True)
          eq 
          (@permutation_ilist_Format m types fin_format formats)
          (permutation_ilist_decoder fin_decoder decoders sort_filter)
          cache_inv
          (@permutation_ilist_Format m types fin_format formats).
  Proof.
    unfold permutation_ilist_Format, permutation_list_Format, SumType_list_Format.
    normalize_format. (*10.1, 10, 10*)

    (*Ahould have used format_sequence_correct as other formats!? ups*)
    eapply sequence_Compose_format_decode_correct; cycle 1.
    (*1*) intros; apply FixList_decode_correct.
      eapply IndexedSumType_Decoder_Correct; eassumption.
    - simpl. intros s v Hsource Hperm.
      split.
      + eapply Permutation_length in Hperm.
        rewrite <- Hperm. 
        eapply ito_list_length. 
      + intros ??; eapply Hinvariants_ok; eauto. 
        eapply Permutation_in; [symmetry|];  eassumption.
    - intros.
      eapply weaken_view_predicate_Proper; cycle 1.
      eapply weaken_source_pred_Proper; cycle 1.
      eapply sort_list_SumType_Correct_Decoder.
      
      unfold flip, pointwise_relation, impl; simpl; tauto.
      unfold flip, pointwise_relation, impl; simpl; tauto.
    - eapply Hcache_inv2.
  Qed.

  (* Some lemmas to make the statment amenable for automation*)

  Lemma SumType_index_lift:
    forall n (types : Vector.t Type n) (h: Type) (y : SumType types),
      (SumType_index (Vector.cons Type h n types) (lift_SumType h y)) =
        Fin.FS (SumType_index types y).
  Proof.
    destruct types.
    - intros; elim y.
    - reflexivity.
  Qed.

  Lemma SumType_proj_lift:
    forall n (types : Vector.t Type n) (h: Type) (y : SumType types),
      let types':= (Vector.cons Type h n types) in
      SumType_proj types y ~= SumType_proj types' (lift_SumType h y).
  Proof.
    destruct types.
    - intros. elim y.
    - reflexivity.
  Qed.
  

  Lemma In_implies_Iterated:
    forall n types (ils: ilist types) (pred: Fin.t n -> Prop),
      IterateBoundedIndex.Iterate_Ensemble_BoundedIndex pred ->
      (forall (x : SumType types),
          In x (@ito_list n types ils) ->
          pred (SumType_index types x)).
  Proof.
    intros.
    eapply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv in H.
    instantiate (1:= SumType_index types x) in H.
    eauto.
  Qed.

  
  Lemma SumType_in_ilist:
    forall {m : nat} (types : Vector.t Type m) ils x, 
      In x (ito_list ils) ->
      ith ils (SumType_index types x) = SumType_proj types x.
  Proof.
    induction types.
    - intros. elim H.
    - intros.
      destruct H; cycle 1.
      + eapply in_map_iff in H.
        destruct H as (y &Heqxy & H).
        eapply IHtypes in H.
        etransitivity; [rewrite <- Heqxy| reflexivity].
        eapply JMeq_eq.
        etransitivity.


        assert (LHS_lemma:
                 forall n (types : Vector.t Type n) (h: Type) (y : SumType types) ,
                   let types':= (Vector.cons Type h n types) in
                   forall  (ils: ilist(B:=id) types'),
                     ith ils (SumType_index types' (lift_SumType h y)) ~=
                       ith ils (Fin.FS (SumType_index types y))).
        {
          clear; intros.
          subst types'.
          erewrite SumType_index_lift.
          econstructor.
        }
        

        eapply LHS_lemma.
        simpl.
        rewrite H.

        eapply SumType_proj_lift.

      + clear IHtypes.
        rewrite <- H.
        destruct types; reflexivity.
  Qed.


  
  (* Version of the lemma written for automation. See each hypothesis for details about why it changed*)
  Lemma Permutation_ilist_decoder_correct: 
    
    forall m (types: Vector.t Type m) cache_inv
           (cache_invariants: Vector.t ((_ -> Prop) -> Prop) m) fin_cache_inv
           (fin_format : FormatM (Fin.t m) ByteString)
           fin_decoder view_fin
           (fin_correct: cache_inv_Property cache_inv fin_cache_inv ->
                         CorrectDecoder ByteStringQueueMonoid view_fin 
                           view_fin eq fin_format fin_decoder cache_inv fin_format)
           (formats : ilist types)
           (invariants: ilist (B:= fun T : Type => T -> Prop) types)
             (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
             (formatrs_decoders_correct : IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                                            (fun idx =>
                                               cache_inv_Property cache_inv (Vector.nth cache_invariants idx)
                                               -> CorrectDecoder
                                                    ByteStringQueueMonoid
                                                    (ith invariants idx)
                                                    (ith invariants idx)
                                                    eq
                                                    (ith formats idx)
                                                    (ith decoders idx)
                                                    cache_inv
                                                    (ith formats idx)))
             
             (* Change the hypothesis to use
                `Iterate_Ensemble_BoundedIndex`, so it can easily be unfolded
                into the list of subproofs. *)
             (Hinvariants_ok: forall (ils : ilist types) (v : list (SumType types)),
                 Permutation (ito_list ils) v ->
                 IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                   (fun idx =>
                      view_fin idx /\
                        ith invariants idx (ith ils idx)
             ))
             (P_inv2:(CacheDecode -> Prop) -> Prop)
             (Hcache_inv2: cache_inv_Property cache_inv
                             (fun P : CacheDecode -> Prop =>
                                (fin_cache_inv P /\
                                   IterateBoundedIndex.Iterate_Ensemble_BoundedIndex'
                                     (fun idx : Fin.t m => Vector.nth cache_invariants idx P)) /\
                                  P_inv2 P)),
        CorrectDecoder ByteStringQueueMonoid
          (constant True) (constant True)
          eq 
          (@permutation_ilist_Format m types fin_format formats)
          (permutation_ilist_decoder fin_decoder decoders sort_filter)
          cache_inv
          (@permutation_ilist_Format m types fin_format formats).
  Proof.
    intros.
    eapply Permutation_ilist_decoder_correct'; try eassumption.
    - (* Turn a quantification of every item in a list with `In`, to an
         iteration ver all the elements with
         `Iterate_Ensemble_BoundedIndex`*)
      
      clear - Hinvariants_ok.
      intros.
      (* remember (fun idx => view_fin (idx) /\ ith invariants (idx) (ith ils idx)) as pred. *)
      replace (SumType_proj types x) with (ith ils (SumType_index types x)); cycle 1.
      { revert H0. eapply SumType_in_ilist.
      }
      cut ((fun y => view_fin y /\ ith invariants y (ith ils y)) (SumType_index types x)); [simpl; auto|].
      eapply In_implies_Iterated; eauto.
  Qed.

  
End ListPermutations.



Section ObjectPermutation.
  (* In this section we wrap the Permutation format around a way to *)

  
  (** *The Format*)
  
  
  (* Like a monadic operation
     `??` in haskell
   *)
  Definition iapp {n:nat} {S:Type} {types:Vector.t Type n}
    (fM: ilist (B:= fun T:Type => S -> T) types) (s:S)
    : ilist (B:= id) types:=
    @imap Type (fun T:Type => S -> T) id (fun _ f => f s) _ _ fM.
  
  Definition to_list {n:nat} {S:Type} {types:Vector.t Type n}
    (projs: ilist (B:= fun T:Type => S -> T) types):= fun s => ito_list (iapp projs s).
  
  Definition permutation_Format
    S (m : nat) (types : Vector.t Type m)
    (projections: ilist (B:= fun T => S -> T) types)
    (fin_format: FormatM (Fin.t m) ByteString)
    (formats: ilist (B:= fun T => FormatM T ByteString) types):
    FormatM S ByteString:=
    permutation_ilist_Format m types fin_format formats ◦ iapp projections.

  (** *The Encoder*)
  
  Definition Permutation_encoder {n} {types: Vector.t Type n}
    (S:Type)
    (projs: ilist (B:= fun T : Type => S -> T) types)
    (encode_fin:   forall sz0 : nat, AlignedEncodeM sz0)
    (encoders: ilist (B:= fun T => forall sz, @AlignedEncodeM _ T sz) types)
    : forall n : nat, AlignedEncodeM n:=
    Projection_AlignedEncodeM (Permutation_ilist_encoder encode_fin encoders) (iapp projs).
  
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
    unfold permutation_Format, Permutation_encoder.
    eapply CorrectAlignedEncoderProjection.
    eapply Permutation_ilist_Encoder_Correct; auto.
  Qed.


  
  (** *The Decoder*)

  Definition permutation_decoder
    {m S}
    {types : Vector.t Type m}
    (fin_decoder : ByteString ->
                   CacheDecode ->
                   option (Fin.t m * ByteString * CacheDecode))
    (decoders : ilist
                  (B:= fun T : Type => @DecodeM (T * ByteString) ByteString
                                         EmptyStore.test_cache) types)
    (decode_ilist : list (SumType types) ->
                    DecodeM (ilist(B:=id) types * ByteString) ByteString)
    (decode_S : ilist(B:=id) types ->
                DecodeM (S * ByteString) ByteString):
    DecodeM (S * ByteString) ByteString:=
    sequence_Decode (permutation_ilist_decoder fin_decoder decoders decode_ilist) decode_S.
  

  Lemma ith_iapp:
    forall S n (types: Vector.t Type n) idx (projs : ilist(B:= fun T => S -> T) types) (s:S),
      ith (iapp projs s) idx = ith projs idx s.
  Proof.
    intros. unfold iapp. rewrite <- ith_imap.
    reflexivity.
  Qed.

  
  (* Version of the lemma written for automation. See each hypothesis for details about why it changed*)
  Lemma Permutation_decoder_Correct: 
    forall (S: Type) m (types: Vector.t Type m)
           (projs: ilist (B:= fun T => S -> T) types) (cache_inv: CacheDecode -> Prop)
           (cache_invariants: Vector.t ((_ -> Prop) -> Prop) m) fin_cache_inv
           (fin_format : FormatM (Fin.t m) ByteString)
           fin_decoder view_fin
           (fin_correct: cache_inv_Property cache_inv fin_cache_inv ->
                         CorrectDecoder ByteStringQueueMonoid view_fin 
                           view_fin eq fin_format fin_decoder cache_inv fin_format)
           (formats : ilist types)
           (source_pred : S -> Prop),
      cache_inv_Property cache_inv
        (fun P : CacheDecode -> Prop =>
           fin_cache_inv P /\
             IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
               (fun idx : Fin.t m => Vector.nth cache_invariants idx P)) ->
      forall (invariants: ilist (B:= fun T : Type => T -> Prop) types)
             (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
             (formatrs_decoders_correct :
               IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                 (fun idx =>
                    cache_inv_Property cache_inv (Vector.nth cache_invariants idx)
                    -> CorrectDecoder
                         ByteStringQueueMonoid
                         (ith invariants idx)
                         (ith invariants idx)
                         eq
                         (ith formats idx)
                         (ith decoders idx)
                         cache_inv
                         (ith formats idx)))
             
             (* Perhaps this is too strong? I don't know if it should
                be prefixed with the source predicate or something. *)
             (Hinvariants_ok: forall (ils : ilist types) (v : list (SumType types)),
                 Permutation (ito_list ils) v ->
                 IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                   (fun idx : Fin.t m => view_fin idx /\ ith invariants idx (ith ils idx))
             )
             (decode_S: ilist(B:=id) types -> DecodeM (S * ByteString) ByteString)
             (* (P_inv2: (CacheDecode -> Prop) -> Prop) *)
      ,
      forall (Decode_S_correct: forall v1 : ilist types,
                 (* cache_inv_Property cache_inv P_inv2 -> *)
                 CorrectDecoder ByteStringQueueMonoid (fun s : S => source_pred s /\ IsProj (iapp projs) v1 s)
                   (fun s : S => source_pred s /\ IsProj (iapp projs) v1 s) eq empty_Format (decode_S v1) cache_inv empty_Format)

      ,
        CorrectDecoder ByteStringQueueMonoid
          source_pred source_pred
          eq 
          (@permutation_Format
             S m types projs fin_format formats
          )
          (permutation_decoder fin_decoder decoders sort_filter decode_S)
          cache_inv
          (@permutation_Format
             S m types projs fin_format formats
          ).
  Proof.
    intros.
    unfold permutation_Format, permutation_decoder.
    (* add an empty format at the end without joining the projections. *)
    Opaque permutation_ilist_Format.
    normalize_format.
    Transparent permutation_ilist_Format.

    eapply format_sequence_correct; eauto; cycle 1.
    - intros.
      eapply @Permutation_ilist_decoder_correct; eauto.

      
    - simpl; tauto.
    - simpl. unfold cache_inv_Property in *; simpl.
      split_and.
      repeat split; auto;

      (* This could be solve by some of the hypothesis we already have
      (e.g. `H0 : fin_cache_inv cache_inv`). But conceptually it
      should be trivial. *)
      [ | ]; (instantiate (1 := constant True)); constructor.
      
  Qed.

  (* Version of the lemma with words as indices *)
  Lemma Permutation_decoder_word_Correct: 
    forall (m0 sz:nat),
      let m:= S m0 in
      forall (types: Vector.t Type m)
        (S: Type)
        (projs: ilist (B:= fun T => S -> T) types) (cache_inv: CacheDecode -> Prop)
        (cache_invariants: Vector.t ((_ -> Prop) -> Prop) m)
        (formats : ilist types)
        (source_pred : S -> Prop)
        (Hineq: (m < pow2 sz)%nat)
        (invariants: ilist (B:= fun T : Type => T -> Prop) types)
        (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
        (Hcache: cache_inv_Property cache_inv
                   (fun P : CacheDecode -> Prop =>
                      IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                        (fun idx : Fin.t m => Vector.nth cache_invariants idx P)))
        (formatrs_decoders_correct : IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                                       (fun idx =>
                                          cache_inv_Property cache_inv (Vector.nth cache_invariants idx)
                                          -> CorrectDecoder
                                              ByteStringQueueMonoid
                                              (ith invariants idx)
                                              (ith invariants idx)
                                              eq
                                              (ith formats idx)
                                              (ith decoders idx)
                                              cache_inv
                                              (ith formats idx)))
        (Hinvariants_ok:
          forall (ils : ilist types) (v : list (SumType types)),
            Permutation (ito_list ils) v ->
            IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
              (fun idx : Fin.t m => ith invariants idx (ith ils idx)))
        (decode_S: ilist(B:=id) types -> DecodeM (S * ByteString) ByteString),
      forall (Decode_S_correct: forall v1 : ilist types,
            CorrectDecoder ByteStringQueueMonoid (fun s : S => source_pred s /\ IsProj (iapp projs) v1 s)
              (fun s : S => source_pred s /\ IsProj (iapp projs) v1 s) eq empty_Format (decode_S v1) cache_inv empty_Format)
      ,
        CorrectDecoder ByteStringQueueMonoid
          source_pred source_pred
          eq 
          (@permutation_Format
             S m types projs (Format_Fin sz) formats
          )
          (permutation_decoder (Fin_Decoder m0 sz) decoders sort_filter decode_S)
          cache_inv
          (@permutation_Format
             S m types projs (Format_Fin sz) formats
          ).
  Proof.
    intros.
    eapply Permutation_decoder_Correct; try eassumption.
    (* used formatrs_decoders_correct  Decode_S_correct *)
    - (* Correctness of the word indices *)
      intros.
      eapply Fin_Decoder_Correct; 
        eassumption.
    - (*uses H*)
      unfold cache_inv_Property in *; simpl in *.
      split; auto.
    - (*uses Hinvariants_ok*)
      clear - Hinvariants_ok Hineq.
      intros. eapply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv.
      intros; split.
      + fold m.
        assert (f2n idx < m)%nat by eapply f2n_ok.
        clear - H0 Hineq.
        lia.
      + apply Hinvariants_ok in H.
        eapply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv in H; eauto.   
  Qed.


  (** *The aligned decoders*)

  Definition AlignedSortList {m} {types: Vector.t Type (S m)}
      (b : list (SumType types)) (numBytes :nat): AlignedDecodeM _ numBytes:=
    Ifopt sortToIlist b as a' Then (return a')%AlignedDecodeM
                                 Else ThrowAlignedDecodeM.
    
  Lemma AlignedDecodeFilter:
    forall m (types: Vector.t Type (S m))
      (b : list (SumType types)) ,
      DecodeMEquivAlignedDecodeM (sort_filter b) (AlignedSortList b).
  Proof.
    unfold sort_filter, filter_decode.
    intros. eapply @AlignedDecode_ifopt.
    eapply Return_DecodeMEquivAlignedDecodeM. 
  Qed.


  (*Move to the indexed sumtype file*)
  Definition IndexedSumTypeAligneDecoder { m} {types: Vector.t Type (S m)}
    (idx_aligned_decoders: forall numBytes : nat, AlignedDecodeM (Fin.t (S m)) numBytes)                    
    (aligned_decoders: ilist
                         (B:= fun T => forall numBytes : nat,
                                  AlignedDecodeM T numBytes) types)
    numBytes: AlignedDecodeM _ numBytes:=
      (a <- idx_aligned_decoders numBytes;
       SumTypeAlignedDecodeM aligned_decoders a)%AlignedDecodeM.
    
    Definition IndexedSumTypeAligneDecoder_fin sz { m} {types: Vector.t Type (S m)}
    (aligned_decoders: ilist
                         (B:= fun T => forall numBytes : nat,
                                  AlignedDecodeM T numBytes) types)
    numBytes: AlignedDecodeM _ numBytes:=
      (a <- IndexAligneDecoder m sz numBytes;
       SumTypeAlignedDecodeM aligned_decoders a)%AlignedDecodeM.

    
    Definition AlignedDecoderPermutation { m} {types: Vector.t Type (S m)} (S:Type)
      idx_aligned_decoders
    (aligned_decoders: ilist
                         (B:= fun T => forall numBytes : nat,
                                  AlignedDecodeM T numBytes) types)
    t (n:nat): AlignedDecodeM S n:=
      (a <- ListAlignedDecodeM (IndexedSumTypeAligneDecoder idx_aligned_decoders aligned_decoders) (Datatypes.S m);
       a0 <- AlignedSortList a n;
       t a0 n)%AlignedDecodeM.
    
    Definition AlignedDecoderPermutation' sz { m} {types: Vector.t Type (S m)} (S:Type)
    (aligned_decoders: ilist
                         (B:= fun T => forall numBytes : nat,
                                  AlignedDecodeM T numBytes) types)
    t (n:nat): AlignedDecodeM S n:=
      (a <- ListAlignedDecodeM (IndexedSumTypeAligneDecoder (IndexAligneDecoder m sz)  aligned_decoders) (Datatypes.S m);
       a0 <- AlignedSortList a n;
       t a0 n)%AlignedDecodeM.
             


  Lemma AlignedDecodePermutation:
    forall m (types: Vector.t Type (S m))
      (S: Type) (decode_S: ilist(B:=id) types -> DecodeM (S * ByteString) ByteString)
      (idx_decoder: DecodeM (Fin.t (Datatypes.S m) * ByteString) ByteString)
      idx_aligned_decoder
      (idx_aligned_decoder_correct: DecodeMEquivAlignedDecodeM idx_decoder idx_aligned_decoder)
      (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
      (t : ilist types ->
           forall numBytes : nat, AlignedDecodeM S numBytes)
      (decoder_S_aligned: forall a : ilist types,
          DecodeMEquivAlignedDecodeM (decode_S a) (t a))
      (aligned_decoders: ilist
                           (B:= fun T => forall numBytes : nat,
                                    AlignedDecodeM T numBytes) types)
      (decoders_aligned: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                           (fun idx : Fin.t (Datatypes.S m) =>
                              DecodeMEquivAlignedDecodeM (ith decoders idx)
                                (ith aligned_decoders idx))),
      DecodeMEquivAlignedDecodeM
        (permutation_decoder idx_decoder decoders sort_filter decode_S)
        (AlignedDecoderPermutation S idx_aligned_decoder aligned_decoders t).
  Proof.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans; [ | intros; reflexivity | ].
    - (* Real goal*)
      unfold permutation_decoder, permutation_ilist_decoder, sequence_Decode.
      eapply @Bind_DecodeMEquivAlignedDecodeM; try eassumption.
      eapply AlignedDecodeListM; cycle 1.
      + (* filter *)
        eapply AlignedDecodeFilter.
      + unfold decoder_IndexedSumType, sequence_Decode.
        eapply @Bind_DecodeMEquivAlignedDecodeM.
        eassumption.
        intro; eapply AlignedDecodeSumTypeM.
        eassumption.
    - intros.
      eapply BindAlignedDecodeM_assoc.
  Qed.
    
  Lemma AlignedDecodePermutation_fin:
    forall sz m (types: Vector.t Type (S m))
      (S: Type) (decode_S: ilist(B:=id) types -> DecodeM (S * ByteString) ByteString)
      (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
      (t : ilist types ->
           forall numBytes : nat, AlignedDecodeM S numBytes)
      (decoder_S_aligned: forall a : ilist types,
          DecodeMEquivAlignedDecodeM (decode_S a) (t a))
      (aligned_decoders: ilist
                           (B:= fun T => forall numBytes : nat,
                                    AlignedDecodeM T numBytes) types)
      (decoders_aligned: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                           (fun idx : Fin.t (Datatypes.S m) =>
                              DecodeMEquivAlignedDecodeM (ith decoders idx)
                                (ith aligned_decoders idx)))
      (cache0: forall (cd : CacheDecode) (n0 m0 : nat),
          addD (addD cd n0) m0 = addD cd (n0 + m0))
      (cache1: forall cd : CacheDecode, addD cd 0 = cd),
      DecodeMEquivAlignedDecodeM
        (permutation_decoder (Fin_Decoder m (sz * 8)) decoders sort_filter decode_S)
        (AlignedDecoderPermutation S (IndexAligneDecoder m sz) aligned_decoders t).
  Proof.
    intros; eapply AlignedDecodePermutation; eauto; eapply @AlignedDecodeFin; assumption.
  Qed.
      
  Lemma AlignedDecodePermutation_enum:
    forall m (types: Vector.t Type (S m)) codes
      (S: Type) (decode_S: ilist(B:=id) types -> DecodeM (S * ByteString) ByteString)
      (decoders: ilist (B:=fun T => DecodeM (T * ByteString) ByteString) types)
      (t : ilist types ->
           forall numBytes : nat, AlignedDecodeM S numBytes)
      (decoder_S_aligned: forall a : ilist types,
          DecodeMEquivAlignedDecodeM (decode_S a) (t a))
      (aligned_decoders: ilist
                           (B:= fun T => forall numBytes : nat,
                                    AlignedDecodeM T numBytes) types)
      (decoders_aligned: IterateBoundedIndex.Iterate_Ensemble_BoundedIndex
                           (fun idx : Fin.t (Datatypes.S m) =>
                              DecodeMEquivAlignedDecodeM (ith decoders idx)
                                (ith aligned_decoders idx)))
      (cache0: forall (cd : CacheDecode) (n0 m0 : nat),
          addD (addD cd n0) m0 = addD cd (n0 + m0))
      (cache1: forall cd : CacheDecode, addD cd 0 = cd),
      DecodeMEquivAlignedDecodeM
        (permutation_decoder (decode_enum codes) decoders sort_filter decode_S)
        (AlignedDecoderPermutation S (Aligned_decode_enum codes) aligned_decoders t).
  Proof.
    intros; eapply AlignedDecodePermutation; eauto.
      
    eapply DecodeMEquivAlignedDecodeM_trans.
     eapply @AlignedDecodeBindEnum.
     eapply Return_DecodeMEquivAlignedDecodeM.
     
    - simpl; intros.
      instantiate(1:= codes).
      unfold DecodeBindOpt2, BindOpt; simpl.
      unfold BinLib.ByteStringQueueMonoid, ByteStringQueueMonoid.
      match goal with
        |- _ = ?X => destruct X as [ [[] ?] |  ]; reflexivity
      end.

    - simpl; intros.
      unshelve eapply ReturnAlignedDecodeM_RightUnit.
      exact S.
  Qed.
  
End ObjectPermutation.


Global Arguments permutation_Format {S m types} projections fin_format formats.
Global Opaque permutation_Format.


Create HintDb resilience.
Global Hint Resolve word_resilience: resilience.
Global Hint Resolve format_enum_resilience: resilience.


(* Instance necessary to invert ilists. *)
Global Instance icons_invert {A B} {a:A} {n:nat} l  :
  ConditionallyInvertibleTwo (@icons _ B a n l) (fun _ _ => True) (ilist_hd') (ilist_tl').
Proof. constructor; reflexivity. Qed.

(* Tactics for applying the correctness lemmas *)
Ltac apply_Permutation_decoder_Correct n types:=
  let types' := eval unfold types in types in
    ilist_of_evar (fun T => DecodeM (T * ByteString) ByteString) types'
      ltac:(fun decoders' =>
              ilist_of_evar (fun T : Type => T -> Prop) types'
                ltac:(fun invariants' =>
                        Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                          ltac:(fun cache_invariants' =>
                                  eapply Permutation_decoder_Correct with
                                  (cache_invariants := cache_invariants')
                                  (invariants:= invariants')
                                  (decoders:= decoders')
           ))).


Ltac split_prim_and :=
  repeat match goal with
      |- IterateBoundedIndex.prim_and ?x ?y =>
        apply IterateBoundedIndex.Build_prim_and
    end; try exact I; simpl; intros.
