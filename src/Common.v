Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega Coq.Lists.SetoidList.
Require Export Coq.Setoids.Setoid Coq.Classes.RelationClasses
        Coq.Program.Program Coq.Classes.Morphisms.

Global Set Implicit Arguments.
Global Generalizable All Variables.

Global Coercion is_true : bool >-> Sortclass.
Coercion bool_of_sumbool {A B} (x : {A} + {B}) : bool := if x then true else false.
Coercion bool_of_sum {A B} (b : sum A B) : bool := if b then true else false.

Lemma bool_of_sum_distr_match {A B C D} (x : sum A B) (c : A -> C) (d : B -> D)
: bool_of_sum (match x with inl k => inl (c k) | inr k => inr (d k) end) = bool_of_sum x.
Proof.
  destruct x; reflexivity.
Qed.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").

(** Runs [abstract] after clearing the environment, solving the goal
    with the tactic associated with [cls <goal type>].  In 8.5, we
    could pass a tactic instead. *)
Tactic Notation "clear" "abstract" constr(cls) :=
  let G := match goal with |- ?G => constr:(G) end in
  let pf := constr:(_ : cls G) in
  let pf' := (eval cbv beta in pf) in
  repeat match goal with
         | [ H : _ |- _ ] => clear H; test (abstract (exact pf'))
         end;
    [ abstract (exact pf') ].

(** fail if [x] is a function application, a dependent product ([fun _
    => _]), or a sigma type ([forall _, _]) *)
Ltac atomic x :=
  idtac;
  match x with
  | _ => is_evar x; fail 1 x "is not atomic (evar)"
  | ?f _ => fail 1 x "is not atomic (application)"
  | (fun _ => _) => fail 1 x "is not atomic (fun)"
  | forall _, _ => fail 1 x "is not atomic (forall)"
  | let x := _ in _ => fail 1 x "is not atomic (let in)"
  | match _ with _ => _ end => fail 1 x "is not atomic (match)"
  | _ => is_fix x; fail 1 x "is not atomic (fix)"
  | context[?E] => (* catch-all *) (not constr_eq E x); fail 1 x "is not atomic (has subterm" E ")"
  | _ => idtac
  end.

(* [pose proof defn], but only if no hypothesis of the same type exists.
   most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn
  end.

(** [pose defn], but only if that hypothesis doesn't exist *)
Tactic Notation "unique" "pose" constr(defn) :=
  match goal with
  | [ H := defn |- _ ] => fail 1
  | _ => pose defn
  end.

(** check's if the given hypothesis has a body, i.e., if [clearbody]
    could ever succeed.  We can't just do [test_tac (clearbody H)],
    because maybe the correctness of the proof depends on the body of
    H *)
Tactic Notation "has" "body" hyp(H) :=
  test (let H' := fresh in pose H as H'; unfold H in H').

Tactic Notation "etransitivity_rev" open_constr(v)
  := match goal with
       | [ |- ?R ?LHS ?RHS ]
         => refine ((fun q p => @transitivity _ R _ LHS v RHS p q) _ _)
     end.
Tactic Notation "etansitivity_rev" := etransitivity_rev _.

(** find the head of the given expression *)
Ltac head expr :=
  match expr with
  | ?f _ => head f
  | _ => expr
  end.

Ltac head_hnf expr := let expr' := eval hnf in expr in head expr'.

(** call [tac H], but first [simpl]ify [H].
    This tactic leaves behind the simplified hypothesis. *)
Ltac simpl_do tac H :=
  let H' := fresh in pose H as H'; simpl; simpl in H'; tac H'.

(** clear the left-over hypothesis after [simpl_do]ing it *)
Ltac simpl_do_clear tac H := simpl_do ltac:(fun H => tac H; try clear H) H.

Ltac simpl_rewrite term := simpl_do_clear ltac:(fun H => rewrite H) term.
Ltac simpl_rewrite_rev term := simpl_do_clear ltac:(fun H => rewrite <- H) term.
Tactic Notation "simpl" "rewrite" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "->" open_constr(term) := simpl_rewrite term.
Tactic Notation "simpl" "rewrite" "<-" open_constr(term) := simpl_rewrite_rev term.

Ltac do_with_hyp tac :=
  match goal with
  | [ H : _ |- _ ] => tac H
  end.

Ltac rewrite_hyp' := do_with_hyp ltac:(fun H => rewrite H).
Ltac rewrite_hyp := repeat rewrite_hyp'.
Ltac rewrite_rev_hyp' := do_with_hyp ltac:(fun H => rewrite <- H).
Ltac rewrite_rev_hyp := repeat rewrite_rev_hyp'.

Ltac apply_hyp' := do_with_hyp ltac:(fun H => apply H).
Ltac apply_hyp := repeat apply_hyp'.
Ltac eapply_hyp' := do_with_hyp ltac:(fun H => eapply H).
Ltac eapply_hyp := repeat eapply_hyp'.

(** solve simple setiod goals that can be solved by [transitivity] *)
Ltac simpl_transitivity :=
  try solve [ match goal with
              | [ _ : ?Rel ?a ?b, _ : ?Rel ?b ?c |- ?Rel ?a ?c ] => transitivity b; assumption
              end ].

(** given a [matcher] that succeeds on some hypotheses and fails on
    others, destruct any matching hypotheses, and then execute [tac]
    after each [destruct].

    The [tac] part exists so that you can, e.g., [simpl in *], to
    speed things up. *)
Ltac do_one_match_then matcher do_tac tac :=
  idtac;
  match goal with
  | [ H : ?T |- _ ]
    => matcher T; do_tac H;
       try match type of H with
           | T => clear H
           end;
       tac
  end.

Ltac do_all_matches_then matcher do_tac tac :=
  repeat do_one_match_then matcher do_tac tac.

Ltac destruct_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => destruct H) tac.
Ltac destruct_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => destruct H) tac.

Ltac inversion_all_matches_then matcher tac :=
  do_all_matches_then matcher ltac:(fun H => inversion H; subst) tac.
Ltac inversion_one_match_then matcher tac :=
  do_one_match_then matcher ltac:(fun H => inversion H; subst) tac.

Ltac destruct_all_matches matcher :=
  destruct_all_matches_then matcher ltac:( simpl in * ).
Ltac destruct_one_match matcher := destruct_one_match_then matcher ltac:( simpl in * ).
Ltac destruct_all_matches' matcher := destruct_all_matches_then matcher idtac.

Ltac inversion_all_matches matcher := inversion_all_matches_then matcher ltac:( simpl in * ).
Ltac inversion_one_match matcher := inversion_one_match_then matcher ltac:( simpl in * ).
Ltac inversion_all_matches' matcher := inversion_all_matches_then matcher idtac.

(* matches anything whose type has a [T] in it *)
Ltac destruct_type_matcher T HT :=
  match HT with
  | context[T] => idtac
  end.
Ltac destruct_type T := destruct_all_matches ltac:(destruct_type_matcher T).
Ltac destruct_type' T := destruct_all_matches' ltac:(destruct_type_matcher T).

Ltac destruct_head_matcher T HT :=
  match head HT with
  | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_one_head T := destruct_one_match ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac inversion_head T := inversion_all_matches ltac:(destruct_head_matcher T).
Ltac inversion_one_head T := inversion_one_match ltac:(destruct_head_matcher T).
Ltac inversion_head' T := inversion_all_matches' ltac:(destruct_head_matcher T).


Ltac head_hnf_matcher T HT :=
  match head_hnf HT with
  | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(head_hnf_matcher T).
Ltac destruct_one_head_hnf T := destruct_one_match ltac:(head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(head_hnf_matcher T).

Ltac inversion_head_hnf T := inversion_all_matches ltac:(head_hnf_matcher T).
Ltac inversion_one_head_hnf T := inversion_one_match ltac:(head_hnf_matcher T).
Ltac inversion_head_hnf' T := inversion_all_matches' ltac:(head_hnf_matcher T).

Ltac destruct_sig_matcher HT :=
  match eval hnf in HT with
  | ex _ => idtac
  | ex2 _ _ => idtac
  | sig _ => idtac
  | sig2 _ _ => idtac
  | sigT _ => idtac
  | sigT2 _ _ => idtac
  | and _ _ => idtac
  | prod _ _ => idtac
  end.
Ltac destruct_sig := destruct_all_matches destruct_sig_matcher.
Ltac destruct_sig' := destruct_all_matches' destruct_sig_matcher.

Ltac destruct_all_hypotheses := destruct_all_matches ltac:(fun HT =>
                                                             destruct_sig_matcher HT || destruct_sig_matcher HT
                                                          ).

(** if progress can be made by [exists _], but it doesn't matter what
    fills in the [_], assume that something exists, and leave the two
    goals of finding a member of the apropriate type, and proving that
    all members of the appropriate type prove the goal *)
Ltac destruct_exists' T := cut T; try (let H := fresh in intro H; exists H).
Ltac destruct_exists := destruct_head_hnf @sigT;
    match goal with
    (*    | [ |- @sig ?T _ ] => destruct_exists' T*)
    | [ |- @sigT ?T _ ] => destruct_exists' T
    (*    | [ |- @sig2 ?T _ _ ] => destruct_exists' T*)
    | [ |- @sigT2 ?T _ _ ] => destruct_exists' T
    end.

(** if the goal can be solved by repeated specialization of some
    hypothesis with other [specialized] hypotheses, solve the goal by
    brute force *)
Ltac specialized_assumption tac := tac;
    match goal with
    | [ x : ?T, H : forall _ : ?T, _ |- _ ] => specialize (H x); specialized_assumption tac
    | _ => assumption
    end.

(** for each hypothesis of type [H : forall _ : ?T, _], if there is
    exactly one hypothesis of type [H' : T], do [specialize (H H')]. *)
Ltac specialize_uniquely :=
  repeat match goal with
         | [ x : ?T, y : ?T, H : _ |- _ ] => test (specialize (H x)); fail 1
         | [ x : ?T, H : _ |- _ ] => specialize (H x)
         end.

(** specialize all hypotheses of type [forall _ : ?T, _] with
    appropriately typed hypotheses *)
Ltac specialize_all_ways_forall :=
  repeat match goal with
         | [ x : ?T, H : forall _ : ?T, _ |- _ ] => unique pose proof (H x)
         end.

(** try to specialize all hypotheses with all other hypotheses.  This
    includes [specialize (H x)] where [H x] requires a coercion from
    the type of [H] to Funclass. *)
Ltac specialize_all_ways :=
  repeat match goal with
         | [ x : ?T, H : _ |- _ ] => unique pose proof (H x)
         end.

(** try to specialize all non-dependent hypotheses using [tac] *)
Ltac specialize_by' tac :=
  idtac;
  match goal with
  | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by tac; specialize (H H'); clear H'
  end.

Ltac specialize_by tac := repeat specialize_by' tac.

Ltac apply_in_hyp lem :=
  match goal with
  | [ H : _ |- _ ] => apply lem in H
  end.

Ltac apply_in_hyp_no_match lem :=
  match goal with
  | [ H : _ |- _ ] => apply lem in H;
      match type of H with
      | appcontext[match _ with _ => _ end] => fail 1
      | _ => idtac
      end
  end.

Ltac apply_in_hyp_no_cbv_match lem :=
  match goal with
  | [ H : _ |- _ ]
    => apply lem in H;
      cbv beta iota in H;
      match type of H with
      | appcontext[match _ with _ => _ end] => fail 1
      | _ => idtac
      end
  end.

(* Coq's build in tactics don't work so well with things like [iff]
   so split them up into multiple hypotheses *)
Ltac split_in_context ident funl funr :=
  repeat match goal with
         | [ H : context p [ident] |- _ ] =>
           let H0 := context p[funl] in let H0' := eval simpl in H0 in assert H0' by (apply H);
                                          let H1 := context p[funr] in let H1' := eval simpl in H1 in assert H1' by (apply H);
                                                                         clear H
         end.

Ltac split_iff := split_in_context iff (fun a b : Prop => a -> b) (fun a b : Prop => b -> a).

Ltac split_and' :=
  repeat match goal with
         | [ H : ?a /\ ?b |- _ ] => let H0 := fresh in let H1 := fresh in
                                                       assert (H0 := fst H); assert (H1 := snd H); clear H
         end.
Ltac split_and := split_and'; split_in_context and (fun a b : Type => a) (fun a b : Type => b).


Ltac destruct_sum_in_match' :=
  match goal with
  | [ H : appcontext[match ?E with inl _ => _ | inr _ => _ end] |- _ ]
    => destruct E
  | [ |- appcontext[match ?E with inl _ => _ | inr _ => _ end] ]
    => destruct E
  end.
Ltac destruct_sum_in_match := repeat destruct_sum_in_match'.

Ltac destruct_ex :=
  repeat match goal with
         | [ H : ex _ |- _ ] => destruct H
         end.

Ltac setoid_rewrite_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite H).
Ltac setoid_rewrite_hyp := repeat setoid_rewrite_hyp'.
Ltac setoid_rewrite_rev_hyp' := do_with_hyp ltac:(fun H => setoid_rewrite <- H).
Ltac setoid_rewrite_rev_hyp := repeat setoid_rewrite_rev_hyp'.

Hint Extern 0 => solve [apply reflexivity] : typeclass_instances.

Ltac set_evars :=
  repeat match goal with
         | [ |- appcontext[?E] ] => is_evar E; let H := fresh in set (H := E)
         end.

Tactic Notation "eunify" open_constr(A) open_constr(B) := unify A B.

Instance pointwise_refl A B (eqB : relation B) `{Reflexive _ eqB} : Reflexive (pointwise_relation A eqB).
Proof.
  compute in *; auto.
Defined.

Instance pointwise_sym A B (eqB : relation B) `{Symmetric _ eqB} : Symmetric (pointwise_relation A eqB).
Proof.
  compute in *; auto.
Defined.

Instance pointwise_transitive A B (eqB : relation B) `{Transitive _ eqB} : Transitive (pointwise_relation A eqB).
Proof.
  compute in *; eauto.
Defined.

Lemma Some_ne_None {T} {x : T} : Some x <> None.
Proof.
  congruence.
Qed.

Lemma None_ne_Some {T} {x : T} : None <> Some x.
Proof.
  congruence.
Qed.

(* We define a wrapper for [if then else] in order for it to play
   nicely with setoid_rewriting. *)
Definition If_Then_Else {A}
           (c : bool)
           (t e : A) :=
  if c then t else e.

Notation "'If' c 'Then' t 'Else' e" :=
  (If_Then_Else c t e)
    (at level 70).

Definition If_Opt_Then_Else {A B}
           (c : option A)
           (t : A -> B)
           (e : B) :=
  match c with
  | Some a => t a
  | None => e
  end.

Notation "'Ifopt' c 'as' c' 'Then' t 'Else' e" :=
  (If_Opt_Then_Else c (fun c' => t) e)
    (at level 70).

Ltac find_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => destruct X
  | [ |- context[If_Then_Else ?X _ _] ] => destruct X
  | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  | [ H : context[If_Then_Else ?X _ _] |- _ ]=> destruct X
  end.

Ltac substs :=
  repeat match goal with
         | [ H : ?x = ?y |- _ ]
           => first [ subst x | subst y ]
         end.

Ltac substss :=
  repeat match goal with
         | [ H : ?x = _ ,
                 H0 : ?x = _ |- _ ]
           => rewrite H in H0
         end.

Ltac injections :=
  repeat match goal with
         | [ H : _ = _ |- _ ]
           => injection H; intros; subst; clear H
         end.


Ltac inversion_by rule :=
  progress repeat first [ progress destruct_ex
                        | progress split_and
                        | apply_in_hyp_no_cbv_match rule ].


Class can_transform_sigma A B := do_transform_sigma : A -> B.

Instance can_transform_sigT_base {A} {P : A -> Type}
  : can_transform_sigma (sigT P) (sigT P) | 0
  := fun x => x.

Instance can_transform_sig_base {A} {P : A -> Prop}
  : can_transform_sigma (sig P) (sig P) | 0
  := fun x => x.

Instance can_transform_sigT {A B B' C'}
         `{forall x : A, can_transform_sigma (B x) (@sigT (B' x) (C' x))}
  : can_transform_sigma (forall x : A, B x)
                        (@sigT (forall x, B' x) (fun b => forall x, C' x (b x))) | 0
  := fun f => existT
                (fun b => forall x : A, C' x (b x))
                (fun x => projT1 (do_transform_sigma (f x)))
                (fun x => projT2 (do_transform_sigma (f x))).

Instance can_transform_sig {A B B' C'}
         `{forall x : A, can_transform_sigma (B x) (@sig (B' x) (C' x))}
  : can_transform_sigma (forall x : A, B x)
                        (@sig (forall x, B' x) (fun b => forall x, C' x (b x))) | 0
  := fun f => exist
                (fun b => forall x : A, C' x (b x))
                (fun x => proj1_sig (do_transform_sigma (f x)))
                (fun x => proj2_sig (do_transform_sigma (f x))).

Ltac split_sig' :=
  match goal with
  | [ H : _ |- _ ]
    => let H' := fresh in
       pose proof (@do_transform_sigma _ _ _ H) as H';
         clear H;
         destruct H'
  end.

Ltac split_sig :=
  repeat split_sig'.

Ltac clearbodies :=
  repeat match goal with
         | [ H := _ |- _ ] => clearbody H
         end.

Ltac subst_body :=
  repeat match goal with
         | [ H := _ |- _ ] => subst H
         end.

(** TODO: Maybe we should replace uses of this with [case_eq], which the stdlib defined for us? *)
Ltac caseEq x := generalize (refl_equal x); pattern x at -1; case x; intros.

Class ReflexiveT A (R : A -> A -> Type) :=
  reflexivityT : forall x, R x x.
Class TransitiveT A (R : A -> A -> Type) :=
  transitivityT : forall x y z, R x y -> R y z -> R x z.
Class PreOrderT A (R : A -> A -> Type) :=
  { PreOrderT_ReflexiveT :> ReflexiveT R;
    PreOrderT_TransitiveT :> TransitiveT R }.
Definition respectful_heteroT A B C D
           (R : A -> B -> Type)
           (R' : forall (x : A) (y : B), C x -> D y -> Type)
           (f : forall x, C x) (g : forall x, D x)
  := forall x y, R x y -> R' x y (f x) (g y).

(* Lifting forall and pointwise relations to multiple arguments. *)
Definition forall_relation2 {A : Type} {B : A -> Type} {C : forall a, B a -> Type} R :=
  forall_relation (fun a => (@forall_relation (B a) (C a) (R a))).
Definition pointwise_relation2 {A B C : Type} (R : relation C) :=
  pointwise_relation A (@pointwise_relation B C R).

Definition forall_relation3 {A : Type} {B : A -> Type}
           {C : forall a, B a -> Type} {D : forall a b, C a b -> Type} R :=
  forall_relation (fun a => (@forall_relation2 (B a) (C a) (D a) (R a))).
Definition pointwise_relation3 {A B C D : Type} (R : relation D) :=
  pointwise_relation A (@pointwise_relation2 B C D R).

Definition forall_relation4 {A : Type} {B : A -> Type}
           {C : forall a, B a -> Type} {D : forall a b, C a b -> Type}
           {E : forall a b c, D a b c -> Type} R :=
  forall_relation (fun a => (@forall_relation3 (B a) (C a) (D a) (E a) (R a))).
Definition pointwise_relation4 {A B C D E : Type} (R : relation E) :=
  pointwise_relation A (@pointwise_relation3 B C D E R).

Ltac higher_order_1_reflexivity' :=
  let a := match goal with |- ?R ?a (?f ?x) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f ?x) => constr:(f) end in
  let x := match goal with |- ?R ?a (?f ?x) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac sym_higher_order_1_reflexivity' :=
  let a := match goal with |- ?R (?f ?x) ?a => constr:(a) end in
  let f := match goal with |- ?R (?f ?x) ?a => constr:(f) end in
  let x := match goal with |- ?R (?f ?x) ?a => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

(* refine is an antisymmetric relation, so we can try to apply
   symmetric versions of higher_order_1_reflexivity. *)

Ltac higher_order_1_reflexivity :=
  solve [ higher_order_1_reflexivity'
        | sym_higher_order_1_reflexivity' ].

Ltac higher_order_1_f_reflexivity :=
  let a := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(a) end in
  let f := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(f) end in
  let x := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

(* This applies reflexivity after refining a method. *)

Ltac higher_order_2_reflexivity' :=
  let x := match goal with |- ?R ?x (?f ?a ?b) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac sym_higher_order_2_reflexivity' :=
  let x := match goal with |- ?R (?f ?a ?b) ?x => constr:(x) end in
  let f := match goal with |- ?R (?f ?a ?b) ?x => constr:(f) end in
  let a := match goal with |- ?R (?f ?a ?b) ?x => constr:(a) end in
  let b := match goal with |- ?R (?f ?a ?b) ?x => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_2_reflexivity :=
  solve [ higher_order_2_reflexivity'
        | sym_higher_order_2_reflexivity' ].

Ltac higher_order_2_f_reflexivity :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_3_reflexivity :=
  let x := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(c) end in
  let x' := (eval pattern a, b, c in x) in
  let f' := match x' with ?f' _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_3_f_reflexivity :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(b) end in
  let c := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(c) end in
  let x' := (eval pattern a, b, c in x) in
  let f' := match x' with ?f' _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_4_reflexivity :=
  let x := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(c) end in
  let d := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(d) end in
  let x' := (eval pattern a, b, c, d in x) in
  let f' := match x' with ?f' _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_4_f_reflexivity :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(b) end in
  let c := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(c) end in
  let d := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(d) end in
  let x' := (eval pattern a, b, c, d in x) in
  let f' := match x' with ?f' _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_reflexivity :=
  match goal with
  | |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) =>  higher_order_4_f_reflexivity
  | |- ?R (?g ?x) (?g' (?f ?a ?b ?c))    =>  higher_order_3_f_reflexivity
  | |- ?R (?g ?x) (?g' (?f ?a ?b))       =>  higher_order_2_f_reflexivity
  | |- ?R (?g ?x) (?g' (?f ?a))          =>  higher_order_1_f_reflexivity

  | |- ?R ?x (?f ?a ?b ?c ?d)           =>  higher_order_4_reflexivity
  | |- ?R ?x (?f ?a ?b ?c)              =>  higher_order_3_reflexivity
  | |- ?R ?x (?f ?a ?b)                 =>  higher_order_2_reflexivity
  | |- ?R ?x (?f ?a)                    =>  higher_order_1_reflexivity

  | |- _                                =>  reflexivity
  end.

Ltac pre_higher_order_reflexivity_single_evar :=
  idtac;
  match goal with
  | [ |- ?L = ?R ] => has_evar R; not has_evar L; symmetry
  | [ |- ?L = ?R ] => has_evar L; not has_evar R
  | [ |- ?L = ?R ] => fail 1 "Goal has evars on both sides of the equality" L "=" R
  | [ |- ?G ] => fail 1 "Goal is not an equality" G
  end.

Ltac higher_order_reflexivity_single_evar_step :=
  clear;
  match goal with
  | [ |- ?f ?x = ?R ] => is_var x; revert x
  | [ |- ?f ?x = ?R ]
    => not has_evar x;
      let R' := (eval pattern x in R) in
      change (f x = R' x)
  end;
  (lazymatch goal with
  | [ |- forall x, ?f x = @?R x ]
    => refine (fun x => f_equal (fun F => F x) (_ : f = R))
  | [ |- ?f ?x = ?R ?x ]
    => refine (f_equal (fun F => F x) (_ : f = R))
   end);
  clear.

Ltac higher_order_reflexivity_single_evar :=
  pre_higher_order_reflexivity_single_evar;
  repeat (reflexivity || higher_order_reflexivity_single_evar_step).

Ltac higher_order_1_reflexivityT' :=
  let a := match goal with |- ?R ?a (?f ?x) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f ?x) => constr:(f) end in
  let x := match goal with |- ?R ?a (?f ?x) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac sym_higher_order_1_reflexivityT' :=
  let a := match goal with |- ?R (?f ?x) ?a => constr:(a) end in
  let f := match goal with |- ?R (?f ?x) ?a => constr:(f) end in
  let x := match goal with |- ?R (?f ?x) ?a => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

(* refine is an antisymmetric relation, so we can try to apply
   symmetric versions of higher_order_1_reflexivityT. *)

Ltac higher_order_1_reflexivityT :=
  solve [ higher_order_1_reflexivityT'
        | sym_higher_order_1_reflexivityT' ].

Ltac higher_order_1_f_reflexivityT :=
  let a := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(a) end in
  let f := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(f) end in
  let x := match goal with |- ?R (?g ?a) (?g' (?f ?x)) => constr:(x) end in
  let a' := (eval pattern x in a) in
  let f' := match a' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

(* This applies reflexivityT after refining a method. *)

Ltac higher_order_2_reflexivityT' :=
  let x := match goal with |- ?R ?x (?f ?a ?b) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac sym_higher_order_2_reflexivityT' :=
  let x := match goal with |- ?R (?f ?a ?b) ?x => constr:(x) end in
  let f := match goal with |- ?R (?f ?a ?b) ?x => constr:(f) end in
  let a := match goal with |- ?R (?f ?a ?b) ?x => constr:(a) end in
  let b := match goal with |- ?R (?f ?a ?b) ?x => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_2_reflexivityT :=
  solve [ higher_order_2_reflexivityT'
        | sym_higher_order_2_reflexivityT' ].

Ltac higher_order_2_f_reflexivityT :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b)) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_3_reflexivityT :=
  let x := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c) => constr:(c) end in
  let x' := (eval pattern a, b, c in x) in
  let f' := match x' with ?f' _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_3_f_reflexivityT :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(b) end in
  let c := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c)) => constr:(c) end in
  let x' := (eval pattern a, b, c in x) in
  let f' := match x' with ?f' _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_4_reflexivityT :=
  let x := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(x) end in
  let f := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(f) end in
  let a := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(a) end in
  let b := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(b) end in
  let c := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(c) end in
  let d := match goal with |- ?R ?x (?f ?a ?b ?c ?d) => constr:(d) end in
  let x' := (eval pattern a, b, c, d in x) in
  let f' := match x' with ?f' _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_4_f_reflexivityT :=
  let x := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(x) end in
  let f := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(f) end in
  let a := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(a) end in
  let b := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(b) end in
  let c := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(c) end in
  let d := match goal with |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) => constr:(d) end in
  let x' := (eval pattern a, b, c, d in x) in
  let f' := match x' with ?f' _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivityT].

Ltac higher_order_0_f_reflexivityT :=
  match goal with
    |- ?R (?g ?a) (?g' ?x) =>
    unify a x; solve [apply reflexivityT]
  end.

Ltac higher_order_reflexivityT :=
  match goal with
  | |- ?R (?g ?x) (?g' (?f ?a ?b ?c ?d)) =>  higher_order_4_f_reflexivityT
  | |- ?R (?g ?x) (?g' (?f ?a ?b ?c))    =>  higher_order_3_f_reflexivityT
  | |- ?R (?g ?x) (?g' (?f ?a ?b))       =>  higher_order_2_f_reflexivityT
  | |- ?R (?g ?x) (?g' (?f ?a))          =>  higher_order_1_f_reflexivityT
  | |- ?R (?g ?a) (?g' ?x)               =>  higher_order_0_f_reflexivityT

  | |- ?R ?x (?f ?a ?b ?c ?d)           =>  higher_order_4_reflexivityT
  | |- ?R ?x (?f ?a ?b ?c)              =>  higher_order_3_reflexivityT
  | |- ?R ?x (?f ?a ?b)                 =>  higher_order_2_reflexivityT
  | |- ?R ?x (?f ?a)                    =>  higher_order_1_reflexivityT

  | |- _                                =>  reflexivityT
  end.

Global Arguments f_equal {A B} f {x y} _ .


Lemma fst_fold_right {A B A'} (f : B -> A -> A) (g : B -> A * A' -> A') a a' ls
  : fst (fold_right (fun b aa' => (f b (fst aa'), g b aa')) (a, a') ls)
    = fold_right f a ls.
Proof.
  induction ls; simpl; trivial.
  rewrite IHls; reflexivity.
Qed.

Lemma if_app {A} (ls1 ls1' ls2 : list A) (b : bool)
  : (if b then ls1 else ls1') ++ ls2 = if b then (ls1 ++ ls2) else (ls1' ++ ls2).
Proof.
  destruct b; reflexivity.
Qed.

Definition pull_if_dep {A B} (P : forall b : bool, A b -> B b) (a : A true) (a' : A false)
           (b : bool)
  : P b (if b as b return A b then a else a') =
    if b as b return B b then P _ a else P _ a'
  := match b with true => eq_refl | false => eq_refl end.

Definition pull_if {A B} (P : A -> B) (a a' : A) (b : bool)
  : P (if b then a else a') = if b then P a else P a'
  := pull_if_dep (fun _ => P) a a' b.

(** From jonikelee@gmail.com on coq-club *)
Ltac simplify_hyp' H :=
  let T := type of H in
  let X := (match eval hnf in T with ?X -> _ => constr:X end) in
  let H' := fresh in
  assert (H' : X) by (tauto || congruence);
    specialize (H H');
    clear H'.

Ltac simplify_hyps :=
  repeat match goal with
         | [ H : ?X -> _ |- _ ] => simplify_hyp' H
         | [ H : ~?X |- _ ] => simplify_hyp' H
         end.

Local Ltac bool_eq_t :=
  destruct_head_hnf bool; simpl;
  repeat (split || intro || destruct_head iff || congruence);
  repeat match goal with
         | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
         | [ H : ?x <> ?x |- _ ] => specialize (H eq_refl)
         | [ H : False |- _ ] => destruct H
         | _ => progress simplify_hyps
         | [ H : ?x = ?y |- _ ] => solve [ inversion H ]
         | [ H : false = true -> _ |- _ ] => clear H
         end.

Lemma bool_true_iff_beq (b0 b1 b2 b3 : bool)
  : (b0 = b1 <-> b2 = b3) <-> (b0 = (if b1
                                     then if b3
                                          then b2
                                          else negb b2
                                     else if b3
                                          then negb b2
                                          else b2)).
Proof. bool_eq_t. Qed.

Lemma bool_true_iff_bneq (b0 b1 b2 b3 : bool)
  : (b0 = b1 <-> b2 <> b3) <-> (b0 = (if b1
                                      then if b3
                                           then negb b2
                                           else b2
                                      else if b3
                                           then b2
                                           else negb b2)).
Proof. bool_eq_t. Qed.

Lemma bool_true_iff_bnneq (b0 b1 b2 b3 : bool)
  : (b0 = b1 <-> ~b2 <> b3) <-> (b0 = (if b1
                                       then if b3
                                            then b2
                                            else negb b2
                                       else if b3
                                            then negb b2
                                            else b2)).
Proof. bool_eq_t. Qed.

Lemma dn_eqb (x y : bool) : ~~(x = y) -> x = y.
Proof.
  destruct x, y; try congruence;
  intro H; exfalso; apply H; congruence.
Qed.

Lemma neq_to_eq_negb (x y : bool) : x <> y -> x = negb y.
Proof.
  destruct x, y; try congruence; try tauto.
Qed.

Lemma InA_In {A} R (ls : list A) x `{Reflexive _ R}
  : List.In x ls -> InA R x ls.
Proof.
  revert x.
  induction ls; simpl; try tauto.
  intros ? [?|?]; subst; [ left | right ]; auto.
Qed.

Lemma InA_In_eq {A} (ls : list A) x
  : InA eq x ls <-> List.In x ls.
Proof.
  split; [ | eapply InA_In; exact _ ].
  revert x.
  induction ls; simpl.
  { intros ? H. inversion H. }
  { intros ? H.
    inversion H; subst;
    first [ left; reflexivity
          | right; eauto ]. }
Qed.

Lemma NoDupA_NoDup {A} R (ls : list A) `{Reflexive _ R}
  : NoDupA R ls -> NoDup ls.
Proof.
  intro H'.
  induction H'; constructor; auto.
  intro H''; apply (@InA_In _ R) in H''; intuition.
Qed.

Lemma push_if_existT {A} (P : A -> Type) (b : bool) (x y : sigT P)
  : (if b then x else y)
    = existT P
             (if b then (projT1 x) else (projT1 y))
             (if b as b return P (if b then (projT1 x) else (projT1 y))
              then projT2 x
              else projT2 y).
Proof.
  destruct b, x, y; reflexivity.
Defined.

(** TODO: Find a better place for these *)
Lemma fold_right_projT1 {A B X} (P : A -> Type) (init : A * B) (ls : list X) (f : X -> A -> A) (g : X -> A -> B -> B) pf pf'
  : List.fold_right (fun (x : X) (acc : A * B) =>
                       (f x (fst acc), g x (fst acc) (snd acc)))
                    init
                    ls
    = let fr := List.fold_right (fun (x : X) (acc : sigT P * B) =>
                                   (existT P (f x (projT1 (fst acc))) (pf' x acc),
                                    g x (projT1 (fst acc)) (snd acc)))
                                (existT P (fst init) pf, snd init)
                                ls in
      (projT1 (fst fr), snd fr).
Proof.
  revert init pf.
  induction ls; simpl; intros [? ?]; trivial; simpl.
  intro.
  simpl in *.
  erewrite IHls; simpl.
  reflexivity.
Qed.

Lemma fold_right_projT1' {A X} (P : A -> Type) (init : A) (ls : list X) (f : X -> A -> A) pf pf'
  : List.fold_right f init ls
    = projT1 (List.fold_right (fun (x : X) (acc : sigT P) =>
                                 existT P (f x (projT1 acc)) (pf' x acc))
                              (existT P init pf)
                              ls).
Proof.
  revert init pf.
  induction ls; simpl; intros; trivial; simpl.
  simpl in *.
  erewrite IHls; simpl.
  reflexivity.
Qed.

Fixpoint combine_sig_helper {T} {P : T -> Prop} (ls : list T) : (forall x, In x ls -> P x) -> list (sig P).
Proof.
  refine match ls with
         | nil => fun _ => nil
         | x::xs => fun H => (exist _ x _)::@combine_sig_helper _ _ xs _
         end;
  clear combine_sig_helper; simpl in *;
  intros;
  apply H;
  first [ left; reflexivity
        | right; assumption ].
Defined.

Lemma Forall_forall1_transparent_helper_1 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
  : P x.
Proof.
  subst; inversion H; repeat subst; assumption.
Defined.
Lemma Forall_forall1_transparent_helper_2 {A P} {x : A} {xs : list A} {l : list A}
      (H : Forall P l) (H' : x::xs = l)
  : Forall P xs.
Proof.
  subst; inversion H; repeat subst; assumption.
Defined.

Fixpoint Forall_forall1_transparent {A} (P : A -> Prop) (l : list A) {struct l}
  : Forall P l -> forall x, In x l -> P x
  := match l as l return Forall P l -> forall x, In x l -> P x with
     | nil => fun _ _ f => match f : False with end
     | x::xs => fun H x' H' =>
                  match H' with
                  | or_introl H'' => eq_rect x
                                             P
                                             (Forall_forall1_transparent_helper_1 H eq_refl)
                                             _
                                             H''
                  | or_intror H'' => @Forall_forall1_transparent A P xs (Forall_forall1_transparent_helper_2 H eq_refl) _ H''
                  end
     end.

Definition combine_sig {T P ls} (H : List.Forall P ls) : list (@sig T P)
  := combine_sig_helper ls (@Forall_forall1_transparent T P ls H).

Arguments Forall_forall1_transparent_helper_1 : simpl never.
Arguments Forall_forall1_transparent_helper_2 : simpl never.

Lemma In_combine_sig {T P ls H x} (H' : In x ls)
  : In (exist P x (@Forall_forall1_transparent T P ls H _ H')) (combine_sig H).
Proof.
  unfold combine_sig.
  induction ls; simpl in *; trivial.
  destruct_head or; subst;
  try first [ left; reflexivity ].
  right.
  revert H.
  match goal with
  | [ |- context[@eq_refl ?A ?a] ] => generalize (@eq_refl A a)
  end.
  set (als := a::ls) in *.
  change als with (a::ls) at 1.
  clearbody als.
  intros e H.
  destruct H; [ exfalso; solve [ inversion e ] | ].
  apply IHls.
Defined.

Fixpoint flatten1 {T} (ls : list (list T)) : list T
  := match ls with
     | nil => nil
     | x::xs => (x ++ flatten1 xs)%list
     end.

Lemma flatten1_length_ne_0 {T} (ls : list (list T)) (H0 : Datatypes.length ls <> 0)
      (H1 : Datatypes.length (hd nil ls) <> 0)
  : Datatypes.length (flatten1 ls) <> 0.
Proof.
  destruct ls as [| [|] ]; simpl in *; auto.
Qed.

Local Hint Constructors List.Forall.

Lemma Forall_app {T} P (ls1 ls2 : list T)
  : List.Forall P ls1 /\ List.Forall P ls2 <-> List.Forall P (ls1 ++ ls2).
Proof.
  split.
  { intros [H1 H2].
    induction H1; simpl; auto. }
  { intro H; split; induction ls1; simpl in *; auto.
    { inversion_clear H; auto. }
    { inversion_clear H; auto. } }
Qed.

Lemma Forall_flatten1 {T ls P}
  : List.Forall P (@flatten1 T ls) <-> List.Forall (List.Forall P) ls.
Proof.
  induction ls; simpl.
  { repeat first [ esplit | intro | constructor ]. }
  { etransitivity; [ symmetry; apply Forall_app | ].
    split_iff.
    split.
    { intros [? ?]; auto. }
    { intro H'; inversion_clear H'; split; auto. } }
Qed.


Lemma Forall_map {A B} {f : A -> B} {ls P}
  : List.Forall P (map f ls) <-> List.Forall (P ∘ f) ls.
Proof.
  induction ls; simpl.
  { repeat first [ esplit | intro | constructor ]. }
  { split_iff.
    split;
      intro H'; inversion_clear H'; auto. }
Qed.

Lemma fold_right_map {A B C} (f : A -> B) g c ls
  : @fold_right C B g
                c
                (map f ls)
    = fold_right (g ∘ f) c ls.
Proof.
  induction ls; unfold compose; simpl; f_equal; auto.
Qed.

Lemma fold_right_orb_true ls
  : fold_right orb true ls = true.
Proof.
  induction ls; destruct_head_hnf bool; simpl in *; trivial.
Qed.

Lemma fold_right_orb b ls
  : fold_right orb b ls = true
    <-> fold_right or (b = true) (map (fun x => x = true) ls).
Proof.
  induction ls; simpl; intros; try reflexivity.
  rewrite <- IHls; clear.
  repeat match goal with
         | _ => assumption
         | _ => split
         | _ => intro
         | _ => progress subst
         | _ => progress simpl in *
         | _ => progress destruct_head or
         | _ => progress destruct_head bool
         | _ => left; reflexivity
         | _ => right; assumption
         end.
Qed.

Local Hint Constructors Exists.

Local Ltac fold_right_orb_map_sig_t :=
  repeat match goal with
         | _ => split
         | _ => intro
         | _ => progress simpl in *
         | _ => progress subst
         | _ => progress destruct_head sumbool
         | _ => progress destruct_head sig
         | _ => progress destruct_head and
         | _ => progress destruct_head or
         | [ H : _ = true |- _ ] => rewrite H
         | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
         | [ H : ?a, H' : ?a -> ?b |- _ ] => specialize (H' H)
         | [ H : ?a, H' : @sig ?a ?P -> ?b |- _ ] => specialize (fun b' => H' (exist P H b'))
         | [ H' : _ /\ _ -> _ |- _ ] => specialize (fun a b => H' (conj a b))
         | [ |- (?a || true)%bool = true ] => destruct a; reflexivity
         | _ => solve [ eauto ]
         | _ => congruence
         end.

Lemma fold_right_orb_map_sig1 {T} f (ls : list T)
  : fold_right orb false (map f ls) = true
    -> sig (fun x => In x ls /\ f x = true).
Proof.
  induction ls; fold_right_orb_map_sig_t.
Qed.

Lemma fold_right_orb_map_sig2 {T} f (ls : list T)
  : sig (fun x => In x ls /\ f x = true)
    -> fold_right orb false (map f ls) = true.
Proof.
  induction ls; fold_right_orb_map_sig_t.
Qed.

Lemma fold_right_orb_map {T} f (ls : list T)
  : fold_right orb false (map f ls) = true
    <-> List.Exists (fun x => f x = true) ls.
Proof.
  induction ls;
  repeat match goal with
         | _ => split
         | _ => intro
         | _ => progress simpl in *
         | [ H : Exists _ [] |- _ ] => solve [ inversion H ]
         | [ H : Exists _ (_::_) |- _ ] => inversion_clear H
         | _ => progress split_iff
         | _ => progress destruct_head sumbool
         | [ H : (_ || _)%bool = true |- _ ] => apply Bool.orb_true_elim in H
         | [ H : ?a, H' : ?a -> ?b |- _ ] => specialize (H' H)
         | [ H : _ = true |- _ ] => rewrite H
         | [ |- (?a || true)%bool = _ ] => destruct a; reflexivity
         | _ => solve [ eauto ]
         | _ => congruence
         end.
Qed.

Lemma fold_right_map_andb_andb {T} x y f g (ls : list T)
  : fold_right andb x (map f ls) = true /\ fold_right andb y (map g ls) = true
    <-> fold_right andb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
Proof.
  induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
  rewrite !Bool.andb_true_iff;
  try tauto.
Qed.

Lemma fold_right_map_andb_orb {T} x y f g (ls : list T)
  : fold_right andb x (map f ls) = true /\ fold_right orb y (map g ls) = true
    -> fold_right orb (andb x y) (map (fun k => andb (f k) (g k)) ls) = true.
Proof.
  induction ls; simpl; intros; destruct_head_hnf bool; try tauto;
  repeat match goal with
         | [ H : _ |- _ ] => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff in H
         | _ => progress rewrite ?Bool.orb_true_iff, ?Bool.andb_true_iff
         end;
  try tauto.
Qed.

Lemma fold_right_map_and_and {T} x y f g (ls : list T)
  : fold_right and x (map f ls) /\ fold_right and y (map g ls)
    <-> fold_right and (x /\ y) (map (fun k => f k /\ g k) ls).
Proof.
  revert x y.
  induction ls; simpl; intros; try reflexivity.
  rewrite <- IHls; clear.
  tauto.
Qed.

Lemma fold_right_map_and_or {T} x y f g (ls : list T)
  : fold_right and x (map f ls) /\ fold_right or y (map g ls)
    -> fold_right or (x /\ y) (map (fun k => f k /\ g k) ls).
Proof.
  revert x y.
  induction ls; simpl; intros; try assumption.
  intuition.
Qed.

Functional Scheme fold_right_rect := Induction for fold_right Sort Type.

Lemma fold_right_andb_map_impl {T} x y f g (ls : list T)
      (H0 : x = true -> y = true)
      (H1 : forall k, f k = true -> g k = true)
  : (fold_right andb x (map f ls) = true -> fold_right andb y (map g ls) = true).
Proof.
  induction ls; simpl; intros; try tauto.
  rewrite IHls; simpl;
  repeat match goal with
         | [ H : _ = true |- _ ] => apply Bool.andb_true_iff in H
         | [ |- _ = true ] => apply Bool.andb_true_iff
         | _ => progress destruct_head and
         | _ => split
         | _ => auto
         end.
Qed.

Lemma fold_right_andb_map_in {A P} {ls : list A} (H : fold_right andb true (map P ls) = true)
  : forall x, List.In x ls -> P x = true.
Proof.
  induction ls; simpl; auto.
  simpl in *.
  apply Bool.andb_true_iff in H; destruct H as [H0 H1].
  specialize (IHls H1).
  intros x [?|?]; subst; simpl in *; auto.
Qed.

Lemma if_ext {T} (b : bool) (f1 f2 : b = true -> T true) (g1 g2 : b = false -> T false)
      (ext_f : forall H, f1 H = f2 H)
      (ext_g : forall H, g1 H = g2 H)
  : (if b as b' return (b = b' -> T b') then f1 else g1) eq_refl
    = (if b as b' return (b = b' -> T b') then f2 else g2) eq_refl.
Proof.
  destruct b; trivial.
Defined.

Class constr_eq_helper {T0 T1} (a : T0) (b : T1) := mkconstr_eq : True.
Hint Extern 0 (constr_eq_helper ?a ?b) => constr_eq a b; exact I : typeclass_instances.
(** return the first hypothesis with head [h] *)
Ltac hyp_with_head h
  := match goal with
     | [ H : ?T |- _ ] => let h' := head T in
                          let test := constr:(_ : constr_eq_helper h' h) in
                          constr:H
     end.
Ltac hyp_with_head_hnf h
  := match goal with
     | [ H : ?T |- _ ] => let h' := head_hnf T in
                          let test := constr:(_ : constr_eq_helper h' h) in
                          constr:H
     end.

Lemma or_False {A} (H : A \/ False) : A.
Proof.
  destruct H as [ a | [] ].
  exact a.
Qed.

Lemma False_or {A} (H : False \/ A) : A.
Proof.
  destruct H as [ [] | a ].
  exact a.
Qed.

Lemma path_prod {A B} {x y : A * B}
      (H : x = y)
  : fst x = fst y /\ snd x = snd y.
Proof.
  destruct H; split; reflexivity.
Defined.

Definition path_prod' {A B} {x x' : A} {y y' : B}
           (H : (x, y) = (x', y'))
  : x = x' /\ y = y'
  := path_prod H.

Lemma lt_irrefl' {n m} (H : n = m) : ~n < m.
Proof.
  subst; apply Lt.lt_irrefl.
Qed.

Lemma or_not_l {A B} (H : A \/ B) (H' : ~A) : B.
Proof.
  destruct H; intuition.
Qed.

Lemma or_not_r {A B} (H : A \/ B) (H' : ~B) : A.
Proof.
  destruct H; intuition.
Qed.

Ltac instantiate_evar :=
  instantiate;
  match goal with
  | [ H : appcontext[?E] |- _ ]
    => is_evar E;
      match goal with
      | [ H' : _ |- _ ] => unify E H'
      end
  | [ |- appcontext[?E] ]
    => is_evar E;
      match goal with
      | [ H' : _ |- _ ] => unify E H'
      end
  end;
  instantiate.

Ltac instantiate_evars :=
  repeat instantiate_evar.

Ltac find_eassumption :=
  match goal with
  | [ H : ?T |- ?T' ] => constr:(H : T')
  end.

Ltac pre_eassumption := idtac; let x := find_eassumption in idtac.

Definition functor_sum {A A' B B'} (f : A -> A') (g : B -> B') (x : sum A B) : sum A' B' :=
  match x with
  | inl a => inl (f a)
  | inr b => inr (g b)
  end.

Lemma impl_sum_match_match_option {A B ret s s' n r}
      {x : option A}
      (f : match x with
           | Some x' => s x'
           | None => n
           end -> ret)
      (g : s' r -> ret)
  : match
      match x return A + B with
      | Some x' => inl x'
      | None => inr r
      end
    with
    | inl x' => s x'
    | inr x' => s' x'
    end -> ret.
Proof.
  destruct x; assumption.
Defined.

Lemma impl_match_option {A ret s n}
      {x : option A}
      (f : forall x', x = Some x' -> s x' -> ret)
      (g : x = None -> n -> ret)
  : match x with
    | Some x' => s x'
    | None => n
    end -> ret.
Proof.
  destruct x; eauto.
Defined.

Definition option_bind {A} {B} (f : A -> option B) (x : option A)
  : option B
  := match x with
     | None => None
     | Some a => f a
     end.

Fixpoint ForallT {T} (P : T -> Type) (ls : list T) : Type
  := match ls return Type with
     | nil => True
     | x::xs => (P x * ForallT P xs)%type
     end.
Fixpoint Forall_tails {T} (P : list T -> Type) (ls : list T) : Type
  := match ls with
     | nil => P nil
     | x::xs => (P (x::xs) * Forall_tails P xs)%type
     end.

Fixpoint Forall_tailsP {T} (P : list T -> Prop) (ls : list T) : Prop
  := match ls with
     | nil => P nil
     | x::xs => (P (x::xs) /\ Forall_tailsP P xs)%type
     end.

Fixpoint ForallT_all {T} {P : T -> Type} (p : forall t, P t) {ls}
  : ForallT P ls
  := match ls with
     | nil => I
     | x::xs => (p _, @ForallT_all T P p xs)
     end.

Fixpoint Forall_tails_all {T} {P : list T -> Type} (p : forall t, P t) {ls}
  : Forall_tails P ls
  := match ls with
     | nil => p _
     | x::xs => (p _, @Forall_tails_all T P p xs)
     end.


Fixpoint ForallT_impl {T} (P P' : T -> Type) (ls : list T) {struct ls}
: ForallT (fun x => P x -> P' x) ls
  -> ForallT P ls
  -> ForallT P' ls
  := match ls return ForallT (fun x => P x -> P' x) ls
                     -> ForallT P ls
                     -> ForallT P' ls
     with
       | nil => fun _ _ => I
       | x::xs => fun H H' => (fst H (fst H'), @ForallT_impl T P P' xs (snd H) (snd H'))
     end.

Ltac free_in x y :=
  idtac;
  match y with
  | appcontext[x] => fail 1 x "appears in" y
  | _ => idtac
  end.

Ltac setoid_subst'' R x :=
  atomic x;
  match goal with
  | [ H : R x ?y |- _ ]
    => free_in x y;
      rewrite ?H;
      repeat setoid_rewrite H;
      repeat match goal with
             | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; rewrite H in H'
             | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; setoid_rewrite H in H'
             end;
      clear H;
      clear x
  | [ H : R ?y x |- _ ]
    => free_in x y;
      rewrite <- ?H;
      repeat setoid_rewrite <- H;
      repeat match goal with
             | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; rewrite <- H in H'
             | [ H' : appcontext[x] |- _ ] => not constr_eq H' H; setoid_rewrite <- H in H'
             end;
      clear H;
      clear x
  end.

Ltac setoid_subst' x :=
  atomic x;
  match goal with
  | [ H : ?R x _ |- _ ] => setoid_subst'' R x
  | [ H : ?R _ x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel' R :=
  idtac;
  match goal with
  | [ H : R ?x _ |- _ ] => setoid_subst'' R x
  | [ H : R _ ?x |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel R := repeat setoid_subst_rel' R.

Ltac setoid_subst_all :=
  repeat match goal with
         | [ H : ?R ?x ?y |- _ ] => atomic x; setoid_subst'' R x
         | [ H : ?R ?x ?y |- _ ] => atomic y; setoid_subst'' R y
         end.

Tactic Notation "setoid_subst" ident(x) := setoid_subst' x.
Tactic Notation "setoid_subst" := setoid_subst_all.

Lemma sub_plus {x y z} (H0 : z <= y) (H1 : y <= x)
  : x - (y - z) = (x - y) + z.
Proof. omega. Qed.

Lemma fold_right_and_iff {A ls}
  : fold_right and A ls <-> (fold_right and True ls /\ A).
Proof.
  induction ls; simpl; tauto.
Qed.

Definition impl0_0 {A} : A -> A := fun x => x.
Definition impl0_1 {A B C} : (B -> C) -> ((A -> B) -> (A -> C)). Proof. auto. Defined.
Definition impl1_1 {A B C} : (B -> A) -> ((A -> C) -> (B -> C)). Proof. auto. Defined.
Definition impl1_2 {A A' B C C'} : ((A -> C) -> (A' -> C')) -> ((A -> B -> C) -> (A' -> B -> C')). Proof. eauto. Defined.

Lemma if_aggregate {A} (b1 b2 : bool) (x y : A)
  : (if b1 then x else if b2 then x else y) = (if (b1 || b2)%bool then x else y).
Proof.
  destruct b1, b2; reflexivity.
Qed.
Lemma if_aggregate2 {A} (b1 b2 b3 : bool) (x y z : A) (H : b1 = false -> b2 = true -> b3 = true -> False)
  : (if b1 then x else if b2 then y else if b3 then x else z) = (if (b1 || b3)%bool then x else if b2 then y else z).
Proof.
  case_eq b1; case_eq b2; case_eq b3; try reflexivity; simpl; intros; exfalso; subst; eauto.
Qed.
Lemma if_aggregate3 {A} (b1 b2 b3 b4 : bool) (x y z w : A) (H : b1 = false -> (b2 || b3)%bool = true -> b4 = true -> False)
  : (if b1 then x else if b2 then y else if b3 then z else if b4 then x else w) = (if (b1 || b4)%bool then x else if b2 then y else if b3 then z else w).
Proof.
  case_eq b1; case_eq b2; case_eq b3; case_eq b4; try reflexivity; simpl; intros; exfalso; subst; eauto.
Qed.

Ltac eassumption' :=
  eassumption
    || match goal with
         | [ H : _ |- _ ] => exact H
       end.

Ltac progress_subgoal top tac cont :=
  top; (tac; try (cont ()) || (try (cont ()))).

(* ltac is call-by-value, so wrap the cont in a function *)
(* local definition in a_u_s *)
Ltac cont_fn top tac'' x :=
  apply_under_subgoal top tac'' with

  (* mutually recursive with progress_subgoal *)
  (* calls top on each subgoal generated, which may generate more subgoals *)
  (* fails when top fails in progress_subgoals *)
  apply_under_subgoal top tac'' :=
    progress_subgoal top tac'' ltac:(cont_fn top tac'').

Ltac doAny srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat srewrite_fn in
  try repeat_srewrite_fn;
    apply_under_subgoal drills_fn ltac:(repeat_srewrite_fn);
    finish_fn.

Ltac set_refine_evar :=
  match goal with
  | |- ?R _ (?H _ _ _ _ _) =>
    let H' := fresh in set (H' := H) in *
  | |- ?R _ (?H _ _ _ _ ) =>
    let H' := fresh in set (H' := H) in *
  | |- ?R _ (?H _ _ _ ) =>
    let H' := fresh in set (H' := H) in *
  | |- ?R _ (?H _ _) =>
    let H' := fresh in set (H' := H) in *
  | |- ?R _ (?H _ ) =>
    let H' := fresh in set (H' := H) in *
  | |- ?R _ (?H ) =>
    let H' := fresh in set (H' := H) in *
  end.
Ltac subst_refine_evar :=
  match goal with
  | |- ?R _ (?H _ _ _ _ _) => subst H
  | |- ?R _ (?H _ _ _ _ ) => subst H
  | |- ?R _ (?H _ _ _ ) => subst H
  | |- ?R _ (?H _ _) => subst H
  | |- ?R _ (?H _ ) => subst H
  | |- ?R _ (?H ) => subst H
  | _ => idtac
  end.
