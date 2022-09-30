(*+ Permutation Examples*)
(* This format allows to encode a record, writting it's fields in any
order. Just like in XML. *)
Require Import Fiat.Narcissus.Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Formats.Reorder.
Require Import Fiat.Narcissus.Formats.PermutationOpt.
Require Import Fiat.Narcissus.Formats.Derived.IndexedSumType.

Require Import Coq.Sorting.Permutation.
Require Import Fiat.Narcissus.Automation.Invertible.

Require Import
  Fiat.Common.ilist
  Fiat.Common.SumType.

Require Import
  Coq.Logic.FinFun.
Import Fin2Restrict.

Set Warnings "-local-declaration".
Set Nested Proofs Allowed.

(* Quick notation for vector *)
Notation "[[ x ; .. ; y ]]" := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) .. ).

(* Quick notation for ilist *)
Notation "{{ x ; .. ; y }}" := (Build_prim_prod x .. (Build_prim_prod y tt) .. ).


(*Ituples are just simple `ilist`s where the type function is trivial. *)
Definition ituple {n} tys: Type:= @ilist _ id n tys.


(** * Simple permutation (two formats)*)
(* | In this module we present the simplest example of using IndexedSumType.
   It encodes either an 8bit woord or an 16bit word.
   The index is encoded using a word directly representing the index.
 *)
Module Permutation.

  Let types:= [word 8:Type; word 16:Type].

  Definition formats : ilist (B := fun T => FormatM T ByteString) types
    := {{ format_word; format_word }}.
  
  Let invariants := ilist_constant_T types.
  Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
  Let invariant := (fun st : SumType types =>
                      view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).

  Record message := {
      label : word 8
    ; data : word 16                     
    }.

  Let myProjections: ilist (B:=fun T => _ -> T) types := {{ label ; data }}.
  Let myTypes {n: nat} {types: Vector.t Type n} {B} (list: ilist (B:=B) types): Vector.t Type n:= types.
  
  Let myCodes: Vector.t (word 8) 2:= [[ natToWord _ 42; natToWord _ 73 ]].
  Let myFinFormat:= (format_enum myCodes).
  
  Let myFormats: ilist (B := fun T => FormatM T ByteString) (myTypes myProjections)
      := {{ format_word; format_word }}.
  
  Let myFormat := False .

  Ltac new_encoder_rules ::=
    eapply Permutation_Encoder_Correct;
    [| unfold Vector.nth; repeat constructor | |IndexedSumType.split_iterate ]; simpl;
    eauto with resilience.
  Definition inv (msg: message):= True.
  
  Let enc_dec : EncoderDecoderPair (permutation_Format myProjections myFinFormat myFormats) inv.
  Proof.
    unfold myFinFormat.
    (* derive_encoder_decoder_pair. *)
    econstructor.
    - synthesize_aligned_encoder.
    - (* synthesize_aligned_decoder*)
      start_synthesizing_decoder.
      + normalize_format.
        (* Set Printing Implicit. *)

        Ltac apply_Permutation_decoder_Correct types:=
          let types' := eval unfold types in types in
            ilist_of_evar (fun T => DecodeM (T * ByteString) ByteString) types'
              ltac:(fun decoders' =>
                      ilist_of_evar (fun T : Type => T -> Prop) types'
                        ltac:(fun invariants' =>
                                Vector_of_evar 2 (Ensembles.Ensemble (CacheDecode -> Prop))
                                  ltac:(fun cache_invariants' =>
                                          eapply Permutation_decoder_Correct with
                                          (cache_invariants := cache_invariants')
                                          (invariants:= invariants')
                                          (decoders:= decoders')
                   ))).
        apply_Permutation_decoder_Correct types;
                                           try solve[apply_rules]; cycle 1.
        *
          (* Add this to the automation of Indexedsumtype*)
          Ltac split_prim_and :=
             repeat match goal with
               |- IterateBoundedIndex.prim_and ?x ?y =>
                 apply IterateBoundedIndex.Build_prim_and
             end; try exact I; simpl; intros.
          simpl; split_prim_and.
          all: apply_rules.
        * intros; simpl; split_prim_and;
            (* This will need to change. Perhaps the correctness lemma
            needs a stronger hypothesis? *)
            auto.
        * intros.
          (* ExtractSource *)
         simpl; intros; eapply CorrectDecoderEmpty.
          -- (* build_fully_determined_type *)
            unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw,
              Basics.compose in *; simpl in *;
              let a' := fresh in
              intros a'; try destruct a'; destruct_conjs;
              unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw in *;
              simpl in *; intros; decompose_source_predicate; subst_projections.
            Transparent iapp.
            unfold iapp; simpl in *.
            repeat subst_invertible_functions_two; reflexivity.
          -- simpl.
             eapply decides_and.
             apply decides_True'.
             
             
             Instance icons_invert {A B} {a:A} {n:nat} l  :
               ConditionallyInvertibleTwo (@icons _ B a n l) (fun _ _ => True) (ilist_hd') (ilist_tl').
             Proof.
               constructor; reflexivity.
             Qed.
             
             unfold IsProj.
             repeat first[blah | apply decides_eq_refl].

             
             match goal with
               |- decides _ (inil = ?x) =>
                 match_inside_prim_snd x
                   ltac:(destruct_ilist)
             end; simpl.
             apply decides_eq_refl.
             
             
        * Transparent cache_inv_Property.
          unfold cache_inv_Property in *; simpl in *; repeat split;
            unfold Vector.nth; simpl in *; auto.
          instantiate(2:= constant True); constructor.
          
      + cbv beta; synthesize_cache_invariant.
      + cbv beta; unfold decode_nat, sequence_Decode;
          optimize_decoder_impl.
      + cbv beta; align_decoders.
        ltac:(cbv beta; unfold decode_nat, sequence_Decode;
              optimize_decoder_impl) ltac:(cbv beta; align_decoders)

                                            Ltac apply_new_combinator_rule ::=
          eapply Permutation_decoder.
        synthesize_aligned_decoder.


        *)
(*



































          
          
          (** * Old  version. *)
          (* This version builds the format from scratch. Great for exploration.

TODO: DELETE when the rest is ready!
           *)
          
          Module PermutationCodes2.  
        Let types:= [word 8:Type; word 16:Type].

        Let myTuple:= ituple types.

        Definition formats : ilist (B := fun T => FormatM T ByteString) types
          := {{ format_word; format_word }}.
        
        Let invariants := ilist_constant_T types.
        Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
        Let invariant := (fun st : SumType types =>
                            view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).

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

        Definition format_SumType_list
          (m : nat) (types : Vector.t Type m)
          (fin_format: FormatM (Fin.t m) ByteString)
          (formats: ilist (B:= fun T => FormatM T ByteString) types):
          FormatM (list (SumType types)) ByteString:=
          format_list (format_IndexedSumType m types formats fin_format).

        
        Definition format_permutation_list
          (m : nat) (types : Vector.t Type m)
          (fin_format: FormatM (Fin.t m) ByteString)
          (formats: ilist (B:= fun T => FormatM T ByteString) types):
          FormatM (list (SumType types)) ByteString:=
          Compose_Format (format_SumType_list m types fin_format formats)
            (Permutation (A:=SumType types)).
        
        
        
        Definition format_through_list
          S
          (m : nat) (types : t Type m)
          (projections: ilist (B:= fun T => S -> T) types)
          (fin_format: FormatM (Fin.t m) ByteString)
          (formats: ilist (B:= fun T => FormatM T ByteString) types):
          FormatM S ByteString:=
          format_permutation_list m types fin_format formats ◦ to_list projections.
        
        Record message := {
            label : word 8
          ; data : word 16                     
          }.

        Let myProjections: ilist (B:=fun T => _ -> T) types := {{ label ; data }}.
        Let myTypes {n: nat} {types: Vector.t Type n} {B} (list: ilist (B:=B) types): Vector.t Type n:= types.
        
        Let myCodes: Vector.t (word 8) 2:= [[ natToWord _ 42; natToWord _ 73 ]].
        Let myFinFormat:= (format_enum myCodes).
        
        Let myFormats: ilist (B := fun T => FormatM T ByteString) (myTypes myProjections) := {{ format_word; format_word }}.
        
        Let myFormat:= format_through_list message _ types myProjections myFinFormat myFormats.
        
        Let enc_dec : EncoderDecoderPair myFormat (constant True).
        Proof.
          (*unfold myFormat,format_through_list, format_permutation_list.*)
          (* derive_encoder_decoder_pair. *)
          econstructor.
          - (* synthesize_aligned_encoder. *)
            start_synthesizing_encoder.
            normalize_encoder_format.
            
            align_encoder_step. (*splits emty*)
            align_encoder_step. (* removes empty*)
            (*eapply CorrectAlignedEncoderProjection.*)
            align_encoder_step. (*projection*)
            
            unfold format_permutation_list.
            match goal with
              |- CorrectAlignedEncoder (Compose_Format ?X _) ?enc =>
                cut (CorrectAlignedEncoder X enc) 
            end.
            + (*This should be trivial, since identity is a premutation*)
              unfold format_SumType_list.
              shelve.
            + repeat align_encoder_step.
          - (* synthesize_aligned_decoder. *)
            start_synthesizing_decoder.
            + Lemma EquivFormat_compose_projection {T S S' S''}
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
                (first_debug
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
              normalize_format. 
              eapply sequence_Compose_format_decode_correct; cycle 1.
              * unfold format_SumType_list.
                unfold myFinFormat.
                (*1*) intros; apply FixList_decode_correct.
                apply_IndexedSumType_Decoder_Correct 2 types.
                unfold Vector.nth; simpl; eapply H.
                simpl;
                  repeat
                    match goal with
                    | |- IterateBoundedIndex.prim_and _ _ =>
                        apply
                          IterateBoundedIndex.Build_prim_and
                    end; try exact I; simpl; 
                  intros.
                3: intros.

                intuition
                  eauto
                    2
                  with data_inv_hints.
                2: { unfold Vector.nth; simpl; eapply H.
                     | .
                     simpl;
                       repeat
                         match goal with
                         | |- IterateBoundedIndex.prim_and _ _ =>
                             apply IterateBoundedIndex.Build_prim_and
                         end; try exact I; simpl; intros. ].
                
                apply_rules.
                
              * intuition; split; try reflexivity.
                etransitivity.
                symmetry; eapply Permutation_length; eauto.
                simpl; reflexivity.
                intros ?.
                match goal with
                | |-
                    context [ fun st b' =>
                                ith _ (SumType_index _ st) (SumType_proj _ st) b' ] =>
                    let a'' := fresh in
                    intro a''; intros;
                    repeat instantiate ( 1 := (constant (constant True)) );
                    repeat destruct a'' as [?| a'']; auto
                | |-
                    context [ fun st b' =>
                                ith _ (SumType_index _ st) (SumType_proj _ st) b' ] =>
                    let a'' := fresh in
                    intro a''; intros;
                    repeat instantiate ( 1 := (constant (constant True)) );
                    repeat destruct a'' as [?| a'']; auto
                end.
                
                solve_side_condition.
                
                intros; split; auto.
                admit.
                shelve.
              * (*ExtractSource. *)
                simpl; intros; eapply CorrectDecoderEmpty.
                -- unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw,
                     Basics.compose in *; simpl in *.
                   let a' := fresh in
                   intros a'; try destruct a'; destruct_conjs.
                   unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw in *;
                     simpl in *; intros. decompose_source_predicate. subst_projections.
                   Require Import Sorting.Sorting.
                   Definition sort: forall A, list A -> list A.
                   Admitted.

                   
                   Definition smart_head {A:Type} (ls: list A): (|ls|) > 0 -> A:=
                     match ls as l return ((| l |) > 0 -> A) with
                     | []%list => fun H : 0 > 0 => ltac:(lia)
                     | a :: ls0 => constant a
                     end.
                   Definition smart_tail {A:Type} (ls: list A): (|ls|) > 0 -> list A:=
                     match ls as l return ((| l |) > 0 -> list A) with
                     | []%list => fun H : 0 > 0 => ltac:(lia)
                     | a :: ls0 => constant ls0
                     end.

                   Lemma smart_list_split_witness:
                     forall {A ls ls'} {x:A} (H: (x::ls')%list = ls),
                       (|ls|) > 0.
                   Proof.
                     intros. destruct ls; simpl in *; try discriminate.
                     unfold ">".
                     lia.
                   Qed.
                   Lemma smart_list_split:
                     forall A ls ls' (x:A) (H: (x::ls')%list = ls),
                       x = smart_head ls (smart_list_split_witness H) /\
                         ls' = smart_tail ls (smart_list_split_witness H).
                   Proof. intros; split; subst ls; reflexivity. Qed.
                   
                   
                   Instance Permutation_ConditionallyInvertibleRel {n}{types: Vector.t Type n}:
                     ConditionallyInvertibleRel (@Permutation (SumType types))
                       (fun a => Sorted eq a) (sort (SumType types)).
                   Proof.
                     constructor.
                     intros.
                   Admitted.

                   Print Instances ConditionallyInvertibleRel.
                   eapply CInvRoundTripRel in H0.
                   Ltac blah:= match goal with
                               | [H: (?a::?ls')%list = ?x |- _ ] =>
                                   let HH:= fresh "HH" in
                                   idtac H;
                                   pose proof (smart_list_split _ _ _ _ H) as HH;
                                   try clear H; destruct HH
                               end.
                   blah.
                   blah.
                   Definition inv_inr: (
                                         clear H0.
                     
                     
                     
                     2: { admit. }

                     Ltac blah:=
                       match goal with
                       | [H: (?a::?ls')%list = ?x |- _ ] => 
                           let HH:= fresh "HH" in
                           destruct x eqn:HH; try discriminate;
                           injection H; try clear H;
                           let H':=fresh in
                           let Hnew_eq:= fresh "Hnew_eq" in
                           intros H' Hnew_eq
                       | [H: ([])%list = ?x |- _ ] =>
                           subst x
                       end.

                     repeat blah.
                     

                     unshelve instantiate(1:=_).
                     
                     
                     
                     match goal with
                     | H:?f ?x ?y
                       |- _ =>
                         eapply CInvRoundTripRel in H;
                         [  | now typeclasses eauto | now simpl in *; eauto ]; 
                         try subst x
                     end.
                     
                     Lemma Permutation_remove
                             
                             
                       subst_invertible. reflexivity).


                   | decide_data_invariant ] ].

                                              
                                              
                                              lazymatch goal with
                                                |- CorrectDecoder ?mon _ _ _ (Compose_Format ?YY ?R ++ _) _ _ _ =>
                                                  remember YY as XX
                                              end.
                                              exploit @sequence_Compose_format_decode_correct.
                                              5:{ intros HH.
                                                  match type of HH with
                                                    CorrectDecoder ByteStringQueueMonoid ?Goal11 
                                                      ?Goal11 eq (Compose_Format ?Goal13 ?Goal10 ++ ?Goal14)
                                                      (sequence_Decode ?Goal15 ?Goal18) ?Goal6
                                                      (Compose_Format ?Goal13 ?Goal10 ++ ?Goal14) =>
                                                      unify Goal11 ((fun _ : message => True));
                                                      try unify Goal13 XX;
                                                      unify Goal10 (fun (a' : message) (b' : list (SumType types)) =>
                                                                      Permutation [inl (label a'); inr (data a')] b') 
                                                  end.
                                                  revert HH.
                                                  lazymatch goal with
                                                    |- CorrectDecoder ByteStringQueueMonoid (constant True) 
                                                         (constant True) eq
                                                         (Compose_Format XX
                                                            (fun (a' : message) (b' : list (SumType types)) =>
                                                               Permutation [inl (label a'); inr (data a')] b') ++ 
                                                            ?Goal9) ?Goal10 ?Goal4
                                                         (Compose_Format XX
                                                            (fun (a' : message) (b' : list (SumType types)) =>
                                                               Permutation [inl (label a'); inr (data a')] b') ++ 
                                                            ?Goal9) ->
                                                       CorrectDecoder AlignedByteString.ByteStringQueueMonoid 
                                                         (constant True) (constant True) eq
                                                         (Compose_Format XX
                                                            (fun (a' : message) (b' : list (SumType types)) =>
                                                               Permutation [inl (label a'); inr (data a')] b') ++ ?empty_Format)
                                                         ?decoder ?cache_inv
                                                         (Compose_Format XX
                                                            (fun (a' : message) (b' : list (SumType types)) =>
                                                               Permutation [inl (label a'); inr (data a')] b')) =>
                                                      unify decoder Goal10;
                                                      unify cache_inv Goal4
                                                  end.
                                                  unshelve instantiate(4:=_). eapply empty_Format.
                                                  intros HH. eapply HH.
                                                  
                                                  eapply HH.
                                                  unshelve instantiate(2:= _) in HH.
                                                  
                                                  eapply HH.
                                                  unfold "◦".
                                                  eapply (format_sequence_correct H) with (monoid :=  AlignedByteString.ByteStringQueueMonoid ).
                                                  * clear H; intros; apply_rules.
                                                    
                                                    exploit @Compose_decode_correct.
                                                    3: { intros HH.
                                                         match type of HH with
                                                           CorrectDecoder ?mon ?g9 ?g10 ?g8 (Compose_Format ?g11 ?g8) ?g13 ?g7 ?g12 =>
                                                             unify g9 g10;
                                                             unify g8 eq;
                                                             unify g11
                                                         end.
                                                         
                                                         
                                                         * clear H. (*solve [ solve_side_condition ].*) shelve.
                                                         * clear H; intros; apply_rules.

                                                           apply_rules.
                                                         + cbv beta; synthesize_cache_invariant.
                                                         + cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
                                                         + cbv beta; align_decoders.
                                                           

                                                           
                                                           Unshelve.
                                                           (* This one is due to way `align_decoders_step`  deals with
       `IterateBoundedIndex.prim_and`.
       There is an already shelved `ilist` that slowly
       decreases but obviously never gets completed (since the last goal doesn't depend).
                                                            *)
                                                           constructor.
                                              Defined.
                                              
                                              Let encode := encoder_impl enc_dec.
                                              
                                              Let decode := decoder_impl enc_dec.
                                              Print Assumptions decode.
                                              
                                              End SumTypeCodes2.

                                              (** * Repeated type*)
                                              (* | In this module show that IndexedSumType, by virtue of using an index, supports repeated types.
   Here the `word 8` type is repeated but, depending on the index, it will use the first or third format.

   We are still using words to directly encode indices
                                               *)

                                              Module SumTypeCodes3.

                                                Let types:= [word 8:Type; word 16:Type; word 8:Type].
                                                Definition formats : ilist (B := fun T => FormatM T ByteString) types
                                                  := {{ format_word; format_word ; format_word }}.

                                                Let invariants := ilist_constant_T types.
                                                
                                                Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.

                                                Let invariant := (fun st : SumType types =>
                                                                    view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).
                                                
                                                Let enc_dec : EncoderDecoderPair (format_IndexedSumType_word 8 formats) invariant.
                                                Proof.
                                                  unfold format_IndexedSumType_word.
                                                  derive_encoder_decoder_pair.
                                                  
                                                  (* (*below are the instructions to do the automation step-by-step*)

      econstructor.
      - synthesize_aligned_encoder.
      - start_synthesizing_decoder.
        + normalize_format.
          (* apply_IndexedSumTypeWord_Decoder_Correct 3 types.
          {intuition
              eauto 2 with data_inv_hints. }  *)
          
          apply_rules.
        + cbv beta; synthesize_cache_invariant.
        + cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
        + cbv beta.
          repeat align_decoders_step. *)
                                                  

                                                  
                                                  (* align_decoders_step' *)
                                                  (* AlignedDecodeSumTypeM *)
                                                  
                                                  Unshelve.
                                                  (* This one is due to way `align_decoders_step`  deals with
           `IterateBoundedIndex.prim_and`.
           There is an already shelved `ilist` that slowly
           decreases but obviously never gets completed (since the last goal doesn't depend).
                                                   *)
                                                  constructor.
                                                Defined.
                                                
                                                Let encode := encoder_impl enc_dec.
                                                
                                                Let decode := decoder_impl enc_dec.
                                                Print Assumptions decode.
                                                
                                              End SumTypeCodes3.


                                              (** * Simple indexed sumtype (two formats)*)
                                              (* | In this module we show different ways to encode the index.  Here
   the index is encoded by a word (representing a label) which is
   looked up in a vector to determine the index.
                                               *)
                                              Module SumTypeCodes_Enum.
                                                
                                                Let types:= [word 8:Type; word 16:Type].
                                                
                                                Definition formats : ilist (B := fun T => FormatM T ByteString) types
                                                  := {{ format_word; format_word }}.
                                                
                                                Let invariants := ilist_constant_T types.
                                                Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
                                                Let constT {T} (a:T):= True.
                                                Let invariant := (fun st : SumType types =>  ((constant True) (SumType_index types st)) /\ ith invariants (SumType_index types st) (SumType_proj types st)).
                                                
                                                Let codes: Vector.t (word 8) 2:= [[ natToWord _ 42; natToWord _ 73 ]].
                                                
                                                Let enc_dec : EncoderDecoderPair (format_IndexedSumType_enum _ codes formats) invariant.
                                                Proof.
                                                  unfold format_IndexedSumType_enum.
                                                  derive_encoder_decoder_pair.

                                                  Unshelve.
                                                  (* This one is due to way `align_decoders_step`  deals with
           `IterateBoundedIndex.prim_and`.
           There is an already shelved `ilist` that slowly
           decreases but obviously never gets completed (since the last goal doesn't depend).
                                                   *)
                                                  constructor.
                                                Defined.
                                                
                                                Let encode := encoder_impl enc_dec.
                                                
                                                Let decode := decoder_impl enc_dec.
                                                
                                              End SumTypeCodes_Enum.


                                              (** * Motivating example*)
                                              (* | Another example using Enum, which originally motivated this format.
                                               *)
                                              Module SumTypeCodes_Enum_Motivate.

                                                (* This was the motivating example, which follows immidiately from out `format_IndexedSumType_enum` *)
                                                Definition format_SumTypeCodes {m} {sz}
                                                  (types : Vector.t Type (S m))
                                                  (formatrs :
                                                    ilist (B := fun T =>
                                                                  T -> CacheFormat -> Comp (ByteString * CacheFormat)) types)
                                                  (codes : Vector.t (word sz) (S m))
                                                  (st : SumType types)
                                                  : CacheFormat -> Comp (ByteString * CacheFormat):=
                                                  format_IndexedSumType_enum m codes formatrs st.

                                                (* Then we can show an example with that format *)
                                                Let types:= [word 8:Type; word 16:Type; word 32:Type; word 16:Type; word 8:Type].
                                                
                                                Definition formats : ilist (B := fun T => FormatM T ByteString) types
                                                  := {{ format_word; format_word; format_word; format_word; format_word }}.
                                                
                                                Let invariants := ilist_constant_T types.
                                                Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
                                                Let constT {T} (a:T):= True.
                                                Let invariant := (fun st : SumType types =>  ((constant True) (SumType_index types st)) /\ ith invariants (SumType_index types st) (SumType_proj types st)).

                                                (* Let's index the entries using prime numbers *)
                                                Let codes: Vector.t (word 8) 5:= [[ natToWord _ 2; natToWord _ 3; natToWord _ 5; natToWord _ 7; natToWord _ 11 ]].

                                                Let enc_dec : EncoderDecoderPair (format_SumTypeCodes types formats codes) invariant.
                                                Proof.
                                                  unfold format_SumTypeCodes, format_IndexedSumType_enum.
                                                  derive_encoder_decoder_pair.

                                                  Unshelve.
                                                  (* This one is due to way `align_decoders_step`  deals with
           `IterateBoundedIndex.prim_and`.
           There is an already shelved `ilist` that slowly
           decreases but obviously never gets completed (since the last goal doesn't depend).
                                                   *)
                                                  constructor.
                                                Defined.
                                                
                                              End SumTypeCodes_Enum_Motivate.
