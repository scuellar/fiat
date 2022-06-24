
Require Import Fiat.Narcissus.Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Formats.Reorder.
Require Import 
        Coq.Sorting.Permutation.
Require Import Fiat.Narcissus.Automation.Invertible.

Require Import
        Fiat.Common.ilist
        Fiat.Common.SumType.

Require Import
        Coq.Logic.FinFun.
Import Fin2Restrict.

Require Import Fiat.Narcissus.Formats.Derived.IndexedSumType.

Set Warnings "-local-declaration".
Set Nested Proofs Allowed.

(* Quick notation for vector *)
Notation "[[ x ; .. ; y ]]" := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) .. ).

(* Quick notation for ilist *)
Notation "{{ x ; .. ; y }}" := (Build_prim_prod x .. (Build_prim_prod y tt) .. ).


(** * Simple indexed sumtype (two formats)*)
(* | In this module we present the simplest example of using IndexedSumType.
   It encodes either an 8bit woord or an 16bit word.
   The index is encoded using a word directly representing the index.
 *)
Module SumTypeCodes2.
  
  Let types:= [word 8:Type; word 16:Type].
  
  Definition formats : ilist (B := fun T => FormatM T ByteString) types
    := {{ format_word; format_word }}.
  
  Let invariants := ilist_constant_T types.
  Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
  Let invariant := (fun st : SumType types =>
                      view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).
  
  Let enc_dec : EncoderDecoderPair (format_IndexedSumType_word 8 formats) invariant.
  Proof.
    unfold format_IndexedSumType_word.
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
