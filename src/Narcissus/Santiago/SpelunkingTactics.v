Require Import
        Fiat.Common (*If_Then_Else If_Opt_Then_Else*)
        Fiat.Common.Tactics.SplitInContext (* split_in_context*)
        .
(** Some useful exploratory tactics. Don't use them in production *)
        
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
