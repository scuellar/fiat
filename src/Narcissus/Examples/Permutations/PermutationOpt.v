(*+ Permutation Examples*)
(* This format allows to encode a record, writting it's fields in any
order. Just like in XML. *)
Require Import Fiat.Narcissus.Examples.TutorialPrelude.
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

Module SimplPermutation.
  (* Simple permutation of two elements, indexed by a code/label *)

  
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
    unfold myFormat, myFinFormat.
    (* derive_encoder_decoder_pair. *)
    econstructor;
      [ synthesize_aligned_encoder |  ].

   (* synthesize_aligned_decoder. *)
   start_synthesizing_decoder.
   - normalize_format. apply_rules.
   - cbv beta; synthesize_cache_invariant.
   - cbv beta; unfold decode_nat, sequence_Decode;
    optimize_decoder_impl.
   - cbv beta; align_decoders.
     
    Unshelve.
    constructor.
  Defined.

  
  Let encode := encoder_impl enc_dec.
  
  Let decode := decoder_impl enc_dec.
  Print Assumptions enc_dec.


End SimplPermutation.

Module FourPermutation.
  (* Just like a SimplPermutation, but encodes five elements. *)

  Let types:= [word 8:Type; word 16:Type; word 32:Type; word 64:Type].
  
  Let invariants := ilist_constant_T types.
  Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
  Let invariant := (fun st : SumType types =>
                      view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).

  Record message := {
      label1 : word 8
    ; label2 : word 16
    ; label3 : word 32
    ; label4 : word 64                   
    }.

  Let myProjections: ilist (B:=fun T => _ -> T) types := {{ label1 ; label2 ; label3 ; label4 }}.
  Let myTypes {n: nat} {types: Vector.t Type n} {B} (list: ilist (B:=B) types): Vector.t Type n:= types.
  
  Let myCodes: Vector.t (word 8) 4:= [[ natToWord _ 1; natToWord _ 2; natToWord _ 3; natToWord _ 4 ]].
  Let myFinFormat:= (format_enum myCodes).
  
  Let myFormats: ilist (B := fun T => FormatM T ByteString) (myTypes myProjections)
      := {{ format_word; format_word; format_word; format_word }}.
  
  Ltac new_encoder_rules ::=
    eapply Permutation_Encoder_Correct;
    [| unfold Vector.nth; repeat constructor | |IndexedSumType.split_iterate ]; simpl;
    eauto with resilience.

  Definition inv (msg: message):= True.

  Definition myFormat:= permutation_Format myProjections myFinFormat myFormats.
    
  Let enc_dec : EncoderDecoderPair myFormat inv.
  Proof.
    unfold myFormat, myFinFormat.
    derive_encoder_decoder_pair.
    
    Unshelve.
    constructor.
  Defined.

  
  Let encode := encoder_impl enc_dec.
  
  Let decode := decoder_impl enc_dec.
  Print Assumptions decode.

  
End FourPermutation.


Module AllEqualPermutation.
  (* Just like a SimplPermutation, but encodes five elements. *)

  Let types:= [word 8:Type; word 8:Type; word 8:Type; word 8:Type].
  
  Let invariants := ilist_constant_T types.
  Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
  Let invariant := (fun st : SumType types =>
                      view_fin (SumType_index types st) /\
                        ith invariants (SumType_index types st) (SumType_proj types st)).

  Record message := {
      label1 : word 8
    ; label2 : word 8
    ; label3 : word 8
    ; label4 : word 8                   
    }.

  Let myProjections: ilist (B:=fun T => _ -> T) types := {{ label1 ; label2 ; label3 ; label4 }}.
  Let myTypes {n: nat} {types: Vector.t Type n} {B} (list: ilist (B:=B) types): Vector.t Type n:= types.
  
  Let myCodes: Vector.t (word 8) 4:= [[ natToWord _ 1; natToWord _ 3; natToWord _ 4; natToWord _ 7 ]].
  Let myFinFormat:= (format_enum myCodes).
  
  Let myFormats: ilist (B := fun T => FormatM T ByteString) (myTypes myProjections)
      := {{ format_word; format_word; format_word; format_word }}.
  
  Ltac new_encoder_rules ::=
    eapply Permutation_Encoder_Correct;
    [| unfold Vector.nth; repeat constructor | |IndexedSumType.split_iterate ]; simpl;
    eauto with resilience.

  Definition inv (msg: message):= True.

  Definition myFormat:= permutation_Format myProjections myFinFormat myFormats.
    
  Let enc_dec : EncoderDecoderPair myFormat inv.
  Proof.
    unfold myFormat, myFinFormat.
    derive_encoder_decoder_pair.
    
    Unshelve.
    constructor.
  Defined.

  
  Let encode := encoder_impl enc_dec.
  
  Let decode := decoder_impl enc_dec.
  
  
  (* Quick goal to explore the decoder *)
  Ltac remember_decoders:=
    match goal with
    | [ |- context [ListAlignedDecodeM (IndexedSumTypeAligneDecoder ?dec1 ?dec2) _] ] =>
        remember dec2 as decoders
    end.
  
  Goal forall m b result, decode m b  = result.
    unfold decode,AlignedDecoderPermutation, AlignedSortList.
    intros; remember_decoders.
  Abort.
  
End AllEqualPermutation.
