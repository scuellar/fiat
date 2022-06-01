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

Section SumTypeCodes.

    Record sensor_msg :=
    { stationID: word 8; data: word 16 }.
  
  Definition format_IndexedSumType_Fin {m} sz
             {types : Vector.t Type m}
             (formats : ilist (B := fun T => FormatM T ByteString) types)
    : FormatM (SumType types) ByteString
    := format_IndexedSumType_full sz formats.

    Let types:= [word 8:Type; word 16:Type].
    Definition formats : ilist (B := fun T => FormatM T ByteString) types
      :=
      {|
        prim_fst := format_word;
        prim_snd := {| prim_fst := format_word; prim_snd := tt |}
      |}.
    Let invariants: ilist (B:= fun T => T -> Prop) types:=
          {|
                    prim_fst := constant True;
                    prim_snd :=
                      {| prim_fst := constant True; prim_snd := tt |}
                  |}.
    Let view_fin {n} (f:Fin.t n):= f2n f < pow2 8.
    Opaque format_IndexedSumType.

    Transparent decoder_IndexedSumType Fin_Decoder.

    Ltac align_decoders_step :=
  first
  [ match goal with
    | |- IterateBoundedIndex.prim_and _ _ =>
          apply IterateBoundedIndex.Build_prim_and; intros;
           [ eapply DecodeMEquivAlignedDecodeM_trans;
              [ 
              | intros; symmetry; cbv beta; simpl;
                 unfold decode_nat, sequence_Decode;
                 optimize_decoder_impl
              | try
                 (instantiate ( 1 := (icons _ _) ); simpl; intros;
                   higher_order_reflexivity) ]
           | try exact I ]
    | |- IterateBoundedIndex.Iterate_Ensemble_BoundedIndex _ =>
          apply IterateBoundedIndex.Build_prim_and; intros;
           [ eapply DecodeMEquivAlignedDecodeM_trans;
              [ 
              | intros; symmetry; cbv beta; simpl;
                 unfold decode_nat, sequence_Decode;
                 optimize_decoder_impl
              | try
                 (instantiate ( 1 := (icons _ _) ); simpl; intros;
                   higher_order_reflexivity) ]
           | try exact I ]
    | |- context [ decode_string_with_term_char ?term_char _ _ ] =>
          eapply (fun H H' => AlignedDecodeStringTermCharM H H' _);
           intros; eauto
    end; idtac "1"
  | eapply @AlignedDecodeDelimiterSimpleM; intros; idtac "2"
  | eapply @AlignedDecodeNatM; intros; idtac "3"
  | eapply @AlignedDecodeByteBufferM; intros; eauto; idtac "4"
  | eapply @AlignedDecodeBind2CharM; intros; eauto; idtac "5"
  | eapply @AlignedDecodeBindCharM; intros; eauto; idtac "6"
  | eapply @AlignedDecodeBind3CharM; intros; eauto; idtac "7"
  | eapply @AlignedDecodeBind4CharM; intros; eauto; idtac "8"
  | eapply @AlignedDecodeBind8CharM; intros; eauto; idtac "9"
  | eapply @AlignedDecodeBindEnum; intros; eauto; idtac "10"
  | let H' := fresh in
    pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 2) as H';
     simpl in H'; eapply H'; eauto; intros; idtac "11"
  | let H' := fresh in
    pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 3) as H';
     simpl in H'; eapply H'; eauto; intros; idtac "12"
  | let H' := fresh in
    pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 4) as H';
     simpl in H'; eapply H'; eauto; intros; idtac "13"
  | eapply @AlignedDecodeBindUnused2CharM; simpl; eauto;
     eapply DecodeMEquivAlignedDecodeM_trans;
     [  | intros; reflexivity |  ]; idtac "14"
  | eapply @AlignedDecodeBindUnusedCharM; simpl; eauto;
     eapply DecodeMEquivAlignedDecodeM_trans;
     [  | intros; reflexivity |  ]; idtac "15"
  | eapply @AlignedDecodeSumTypeM; intros; eauto; idtac "16"
  | eapply @AlignedDecodeListM; intros; eauto; idtac "17"
  | eapply @AlignedDecodeCharM; intros; eauto; idtac "18"
  | eapply (fun H H' => AlignedDecodeNCharM H H'); eauto; simpl; intros; idtac "19"
  | eapply (fun H H' => AlignedDecodeNCharM H H'); eauto; simpl; intros; idtac "20"
  | eapply (fun H H' => AlignedDecodeNCharM H H'); eauto; simpl; intros; idtac "21"
  | eapply (AlignedDecodeNUnusedCharM _ _); eauto; simpl; intros; idtac "22"
  | eapply @AlignedDecode_shift_if_Sumb; idtac "23"
  | eapply @AlignedDecode_shift_if_bool; idtac "24"
  | eapply @Return_DecodeMEquivAlignedDecodeM; idtac "25"
  | eapply @AlignedDecode_Sumb; idtac "26"
  | eapply AlignedDecode_ifopt; intros; idtac "27"
  | match goal with
    | |-
      DecodeMEquivAlignedDecodeM
        (fun b c => Ifopt _ as c' Then _ c' Else _) _ =>
          eapply DecodeMEquivAlignedDecodeM_trans;
           [ eapply AlignedDecode_ifopt
           | intros; reflexivity
           | intros; higher_order_reflexivity ]; 
           intros
    end; idtac "28"
  | let H := fresh in
    pose proof @AlignedDecode_if_Sumb_dep as H; eapply H; clear H;
     [ solve [ eauto ] | solve [ eauto ] |  |  ] ; idtac "29"
  | eapply @AlignedDecode_ifb; idtac "30"
  | eapply @AlignedDecode_ifb_both; idtac "31"
  | eapply @AlignedDecode_ifb_dep;
     [ solve [ eauto ] | solve [ eauto ] |  |  ]; idtac "32"
  | eapply @AlignedDecodeBindOption; intros; eauto; idtac "33"
  | eapply @AlignedDecode_Throw; idtac "34"
  | intros; higher_order_reflexivity; idtac "35"
  | eapply @AlignedDecode_CollapseEnumWord; idtac "36"
  | eapply @AlignedDecode_CollapseWord'; eauto
     using decode_word_eq_decode_unused_word,
       decode_word_eq_decode_bool, decode_word_eq_decode_nat,
       decode_word_eq_decode_word; idtac "37"
  | eapply @AlignedDecodeBindDuplicate;
     [ simpl; intros; f_equiv; apply functional_extensionality; intros;
        repeat (apply functional_extensionality; intros); symmetry;
        repeat
         match goal with
         | |- (if ?b then ?tt else ?te) = ?t' (?f ?d) ?a ?v' ?cd =>
               etransitivity;
                [ eapply (FindFuncIf a v' cd b d f tt te);
                   [ try higher_order_reflexivity
                   | higher_order_reflexivity
                   | higher_order_reflexivity ]
                | higher_order_reflexivity ]
         | |-
           (`(a, t'', cd'') <- ?decode_A' ?v' ?cd';
            @?t' a t'' cd'') = _ ?d' _ _ _ =>
               etransitivity;
                [ eapply FindFuncBind with (decode_A := decode_A')
                   (v0 := v') (cd0 := cd') (t := t') (
                   d := d'); intros
                | higher_order_reflexivity ]
         end; idtac "38"
     | simpl; intros; idtac "39"
     | intros; eapply functional_extensionality_dep; intros; eauto; idtac "40"
     | intros; eapply functional_extensionality_dep; intros; eauto; idtac "41" ]; idtac "42" ].


          Definition IndexedSumTypeAligneDecoder (n numBytes : nat):
              AlignedDecodeM (Fin.t (S n)) numBytes:=
                  b <- GetCurrentByte;
            (fun (b0 : word 8) (sz : nat) =>
               if
                 (lt_dec (@f2n (S n) (word2Fin b0)) (pow2 8) &&
                    weqb (@fin2Word (S n) 8 (word2Fin b0)) b0)%bool
               then (fun numBytes0 : nat => return (word2Fin b0)) sz
               else fail) b numBytes.
          Lemma blah:
            DecodeMEquivAlignedDecodeM
               (Fin_Decoder 1 8) (IndexedSumTypeAligneDecoder 1).
          Proof.
            unfold Fin_Decoder, sequence_Decode.
            eapply @AlignedDecodeBindCharM; intros; eauto.
            eapply @AlignedDecode_ifb.
            eapply @Return_DecodeMEquivAlignedDecodeM.
          Defined.
      
      Lemma blah' {C: Type}:
        forall (t: Fin.t 2 -> DecodeM (C * ByteString) ByteString)
          (t': Fin.t 2 -> forall numBytes : nat, AlignedDecodeM C numBytes),
        (forall a, DecodeMEquivAlignedDecodeM (t a) (t' a))-> 
        DecodeMEquivAlignedDecodeM
          (fun b cd =>
             `(a, b0, env) <- Fin_Decoder 1 8 b cd;
           t a b0 env)
          (fun numBytes =>
             a <- IndexedSumTypeAligneDecoder 1 numBytes;
          t' a numBytes).
          Proof.
            intros.
            eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
            eapply blah.
          Defined.


    
    Let enc_dec : EncoderDecoderPair (format_IndexedSumType_Fin 8 formats)
                                     (fun st : SumType types =>
                                        view_fin (SumType_index types st) /\ ith invariants (SumType_index types st) (SumType_proj types st)).
    Proof. (*derive_encoder_decoder_pair.*)
      unfold format_IndexedSumType_Fin, format_IndexedSumType_full, Format_Fin.
      constructor.
      - synthesize_aligned_encoder. 

      - (* synthesize_aligned_decoder. *)
        start_synthesizing_decoder.
        + normalize_format; apply_rules.
        + cbv beta; synthesize_cache_invariant. 
        + cbv beta; unfold decode_nat, sequence_Decode.
          Opaque decode_SumType.
          optimize_decoder_impl.
        + eapply blah'.
          
          
            
          Lemma DecodeBindOpt2_empty S T1 T2 (F: DecodeM (S * T1) T2) : 
            forall (b0 : T2) (cd : ()),
              (`(l, bs, cd') <- F b0 cd;
               Some (l, bs, cd')) = F b0 cd.
          Proof.
            intros.
            unfold DecodeBindOpt2, BindOpt; simpl.
            destruct (F b0 cd) as [[ [? ?] ?] |]; reflexivity.
          Qed.
          
          eapply DecodeMEquivAlignedDecodeM_trans; cycle 2.
          reflexivity.
          eapply @AlignedDecodeSumTypeM.
          3:{ simpl.
              (* unshelve(instantiate (1 := _)). *)
              (* intros x y z. exact (Some (x,y,z)). *)
              eapply DecodeBindOpt2_empty.
          }
          2:{ align_decoders_step. }
          apply IterateBoundedIndex.Build_prim_and; intros.
          { eapply DecodeMEquivAlignedDecodeM_trans; cycle 1.
            * intros; symmetry; cbv beta; simpl;
                unfold decode_nat, sequence_Decode.
              reflexivity.
            *  (instantiate ( 1 := (icons _ _) ); simpl; intros;
                higher_order_reflexivity).
            * eapply DecodeMEquivAlignedDecodeM_trans; cycle 2.
              reflexivity.
              eapply @AlignedDecodeCharM.
              reflexivity. }
          apply IterateBoundedIndex.Build_prim_and; intros; try exact I.
          * eapply DecodeMEquivAlignedDecodeM_trans; cycle 1.
            -- intros; symmetry; cbv beta; simpl;
              unfold decode_nat, sequence_Decode.
            reflexivity.
             --  (instantiate ( 1 := (icons _ _) ); simpl; intros;
                  higher_order_reflexivity).
             -- eapply DecodeMEquivAlignedDecodeM_trans; cycle 2.
                reflexivity.
                eapply @AlignedDecodeBind2CharM.
                reflexivity.
                eapply Return_DecodeMEquivAlignedDecodeM.
                eapply DecodeBindOpt2_empty.
                


            Unshelve.
            all: try constructor.
    Defined.
    
  Let encode := encoder_impl enc_dec.
  
  Let decode := decoder_impl enc_dec.
  
End SumTypeCodes.
