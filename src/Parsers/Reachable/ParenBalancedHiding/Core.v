Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Export Coq.Classes.RelationPairs.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Context (G : grammar Char).

  (**
<<
pbh' ch n "" = (n == 0)
pbh' ch n (ch :: s) = n > 0 && pbh' ch n s
pbh' ch n ('(' :: s) = pbh' ch (n + 1) s
pbh' ch n (')' :: s) = n > 0 && pbh' ch (n - 1) s
pbh' ch n (_ :: s) = pbh' ch n s

pbh = pbh' '+' 0
>>
*)

  Definition pbh_check_level (ch : Char) (start_level : nat) : bool
    := pb_check_level true ch start_level.

  Definition pbh_new_level (ch : Char) (start_level : nat) : nat
    := pb_new_level ch start_level.

  Section generic.
    Context (transform_valid : nonterminals_listT -> string -> nonterminals_listT)
            (valid0 : nonterminals_listT).

    Inductive generic_pbh'_productions : nonterminals_listT -> productions Char -> Type :=
    | PBHNil : forall valid,
                 generic_pbh'_productions valid nil
    | PBHCons : forall valid pat pats,
                  generic_pbh'_production valid 0 pat
                  -> generic_pbh'_productions valid pats
                  -> generic_pbh'_productions valid (pat::pats)
    with generic_pbh'_production : nonterminals_listT -> nat -> production Char -> Type :=
    | PBHProductionNil : forall valid,
                           generic_pbh'_production valid 0 nil
    | PBHProductionConsNonTerminal0 : forall valid nt its,
                                        is_valid_nonterminal valid nt
                                        -> generic_pbh'_productions (transform_valid valid nt) (Lookup G nt)
                                        -> generic_pbh'_production valid 0 its
                                        -> generic_pbh'_production valid 0 (NonTerminal nt :: its)
    | PBHProductionConsNonTerminalS : forall valid start_level nt its,
                                        pb'_production G valid0 0 (NonTerminal nt :: nil)
                                        -> generic_pbh'_production valid (S start_level) its
                                        -> generic_pbh'_production valid (S start_level) (NonTerminal nt :: its)
    | PBHProductionConsTerminal : forall valid start_level ch its,
                                    pbh_check_level ch start_level
                                    -> generic_pbh'_production valid (pbh_new_level ch start_level) its
                                    -> generic_pbh'_production valid start_level (Terminal ch :: its).
  End generic.

  Definition minimal_pbh'_productions := generic_pbh'_productions remove_nonterminal.
  Definition minimal_pbh'_production := generic_pbh'_production remove_nonterminal.

  Definition pbh'_productions := generic_pbh'_productions (fun valid _ => valid).
  Definition pbh'_production := generic_pbh'_production (fun valid _ => valid).
End cfg.
