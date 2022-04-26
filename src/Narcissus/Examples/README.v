
Require Import Fiat.Narcissus.Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Formats.Reorder.
Require Import 
        Coq.Sorting.Permutation.
Require Import Fiat.Narcissus.Automation.Invertible.

Set Warnings "-local-declaration".
Set Nested Proofs Allowed.
(**
The following section presents the Narcissus framework through a series of increasingly complex examples showcasing its main features.  Details are purposefuly omitted; they will be revealed in section N.  The end result is a moderately complex description for the packet format used by an indoor temperature sensor to report measurements to a smart home controller.
**)

(**
We start with an extremely simple record, and a correspondingly simple format:
**)

(*Module Example.

Require Import ilist
        SumType.

Definition instr : Type := SumType [word 8 : Type; word 8 : Type].

Definition instr_codes : t (word 8) 2 :=
  [ natToWord 8 5; natToWord 8 43].

Let invariant (i : instr) := True.

Definition format_instr : FormatM instr ByteString :=
  format_enum instr_codes ◦ (SumType_index _) ++ (* Format the tag for the instructions *)
  format_SumType _ (icons format_word (icons format_word inil)) ◦ (@id _) (* Format the argment for the instructions *)
.

Let no_align_decode : CorrectDecoderFor invariant format_instr.
 Proof.
   Solver.start_synthesizing_decoder.
   NormalizeFormats.normalize_format; apply_rules.
   last_failing_goal.
   revert H.
   match goal with
     | |- context [ CorrectDecoder (T := ?B) _ _ _ _ (format_SumType (m := ?n)  ?types _) _ _ _ ] =>
          let cache_inv_H := fresh in
          intros cache_inv_H; (first
           [ let types' := eval unfold types in types in
             ilist_of_evar (fun T : Type => T -> CacheFormat -> Comp (B * CacheFormat)) types'
              ltac:(fun formatrs' =>
                      ilist_of_evar (fun T : Type => B -> CacheDecode -> option (T * B * CacheDecode)) types'
                       ltac:(fun decoders' =>
                               ilist_of_evar (fun T : Type => Ensembles.Ensemble T) types'
                                ltac:(fun invariants' =>
                                        ilist_of_evar (fun T : Type => T -> B -> Prop) types'
                                                  ltac:(fun cache_invariants' =>
                                                          eapply (SumType_decode_correct types) with
                                                            (formatrs := formatrs') (
                                                           decoders := decoders') (invariants := invariants')
                                                           (cache_invariants := cache_invariants')))));
              apply_rules
           | ilist_of_evar (fun T : Type => T -> CacheFormat -> Comp (B * CacheFormat)) types
              ltac:(fun formatrs' =>
                      ilist_of_evar (fun T : Type => B -> CacheDecode -> option (T * B * CacheDecode)) types
                       ltac:(fun decoders' =>
                               ilist_of_evar (fun T : Type => Ensembles.Ensemble T) types
                                ltac:(fun invariants' =>
                                                 Vector_of_evar n (Ensembles.Ensemble (CacheDecode -> Prop))
                                                  ltac:(fun cache_invariants' =>
                                                          eapply (SumType_decode_correct types) with
                                                            (formatrs := formatrs') (
                                                              decoders := decoders') (invariants := invariants')
                                                            (cache_invariants := cache_invariants'))))) ]);
          [ simpl; repeat (apply IterateBoundedIndex.Build_prim_and; intros ** ); try exact I; apply_rules
                          | apply cache_inv_H ]; intros
             end.
            intros; simpl.
            unfold IsProj in H1.
            intuition eauto.
            destruct s; simpl; eauto.
            intros; apply_rules.
            simpl; intros;
              eapply CorrectDecoderEmpty.
            unfold Basics.compose in *;
              simpl in *;
              let a' := fresh in
              intros a'; repeat destruct a' as [? a'];
                (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
                simpl in *; intros;
                  (* Decompose data predicate *)
                  decompose_source_predicate;
                  (* Substitute any inferred equalities; decomposing *)
                  (* any product types that might have been built up *)
                  (* along the way *)
                  subst_projections.
            eapply H1.
            decide_data_invariant.
            simpl.
            instantiate (1 := fun _ => True).
            instantiate (1 := fun _ => True).
            apply unfold_cache_inv_Property; compute; intuition.
            cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
            Defined.


Inductive instr : Type :=
  | ADDI: word 8 -> instr    (* 05 iw *)
  | SUBI: word 8 -> instr.   (* 2D iw *)


Definition *)

(* Module Sensor_test. *)
(*   Record sensor_msg := *)
(*     { stationID: word 8; stationID': word 8; data: word 16 }. *)

(*   Let format := *)
(*        format_word ◦ stationID' *)
(*     ++ format_word ◦ stationID *)
(*     ++ format_word ◦ data. *)
  
(*   Let format' := *)
(*        format_word ◦ stationID *)
(*     ++ format_word ◦ stationID *)
(*     ++ format_word ◦ data. *)

(*   Let invariant (msg: sensor_msg) := *)
(*     True. *)
(*   Let enc_dec : EncoderDecoderPair format' invariant. *)
(*   Proof. derive_encoder_decoder_pair. Defined. *)

(*   Let encode := encoder_impl enc_dec. *)
(*   Let decode := decoder_impl enc_dec. *)

(*   Goal forall a b c, decode a b = Some c -> False. *)
(*     unfold decode. *)
(*     un *)

(*Some Helpful tactics*)

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

Module ReorderTest.
  Record sensor_msg :=
    { stationID: word 8; data: word 16 }.

  
  (* The predicate fro the permutation *)
  Definition idMap (msg: sensor_msg):
    list (@SumType.SumType 2 [((word 8):Type); ((word 16):Type)]).
  Proof.
    right; [|right;[|left]].
    + left. apply stationID; auto.
    + right. apply data; auto.
  Defined.
  (* This is the simple reorder *)
  Definition IsReorder' (msg: sensor_msg) ls :=
    Permutation (idMap msg) ls.
  (* This is the predicate that helps the view get extracted! *)
  Definition inver_reordering' (ls: list (SumType.SumType [word 8:Type; word 16:Type])):
    option sensor_msg.
  Proof.
    destruct ls as [| s1 ls]; [|destruct ls as [|s2 ls]; [|destruct ls]].
    - (* empty. *)
      exact None.
    - (* just one element*)
      exact None.
    - (* two elements *)
      destruct s1; destruct s2.
      + (* s1 s2 : word 8 *)
        exact None.
      + left; constructor; assumption.
      + left; constructor; assumption.
      + (* s1 s2 : word 16 *)
        exact None.
    - (* too many elements *)
      exact None.
  Defined.
  Definition invert_reordering (ls: list (SumType.SumType [word 8:Type; word 16:Type])):
    option sensor_msg:=
    match ls with
    | []%list => None
    | [s1]%list => None
    | [s1; s2]%list =>
        match s1, s2 with
        | inl _, inl _ => None
        | inl w, inr w0 => Some {| stationID := w; data := w0 |}
        | inr w, inl w0 => Some {| stationID := w0; data := w |}
        | inr _, inr _ => None 
        end
    | s1 :: s2 :: _ :: _ => None
    end.
  Definition IsReorder (msg: sensor_msg) ls :=
    invert_reordering ls = Some msg.
  
      
  
  Definition types: t Type 2:=[word 8:Type; word 16:Type].
  
  Definition formats: ilist.ilist (B:=fun V => FormatM V ByteString) types:=
    {|
      ilist.prim_fst := format_word;
      ilist.prim_snd :=
      {| ilist.prim_fst := format_word; ilist.prim_snd := tt |}
    |}.
  Definition format': sensor_msg -> CacheFormat -> Comp (ByteString * CacheFormat).
  Proof.
    unshelve eapply Permutation_Format; cycle 1.
    { exact types. }

    { (*Indexed sumtype *)
      unfold FormatM.
      (* apply format_indexed_SumType. *)
      apply (format_word_SumType 8).
      - (* formats *)
        exact formats. }

    { (* The reordering predicate *)
      exact IsReorder. }
  Defined.
  
  Require Import Fiat.Common.ilist.
  Definition format: sensor_msg -> CacheFormat -> Comp (ByteString * CacheFormat):=
    Permutation_Format types
                       (format_word_SumType 8 types formats)
                       IsReorder.
    
  Let invariant (msg: sensor_msg) :=
        True.

  
      Lemma CorrectAlignedEncoder_Projection2Compose
        : forall S S' (F: S -> S' -> Prop) (format_S : FormatM S' ByteString)
            (f : S -> S')
            (encode : forall sz : nat, AlignedEncodeM sz),
          (forall x y, f x = y -> F x y) ->
          CorrectAlignedEncoder (format_S ◦ f)
                                (Projection_AlignedEncodeM encode f) -> 
          CorrectAlignedEncoder (Compose_Format format_S F)
                                (Projection_AlignedEncodeM encode f).
      Proof. Admitted.
      Lemma Permutation_eq {T}: 
          forall (l1 l2:list T), l1 = l2 -> Permutation l1 l2.
  Proof. intros; subst; apply Permutation_refl. Qed.
  Lemma IsReorder_ID: forall x, IsReorder x (idMap x).
        Proof. intros x; destruct x; simpl. reflexivity. Qed.
        
  Lemma SimplPrimFst:
    forall A B (P: A -> Type),
    forall a, P a -> forall (b:B),
        P (ilist.prim_fst {| ilist.prim_fst:= a; ilist.prim_snd:= b |} ).
  Proof. auto. Qed.
          


  (* The empty format should be added automatically! *)
  Let enc_dec : EncoderDecoderPair (format ++ empty_Format) invariant.
  Proof.
    
    econstructor. (* derive_encoder_decoder_pair *)
    - unfold format, types, Permutation_Format, format_word_SumType, format_indexed_SumType. (* types. *)

      (* Encoder *)
      (*synthesize_aligned_encoder.*)
      start_synthesizing_encoder.
      normalize_encoder_format. (*Does nothing*)
      (* Try directly deriving *)
      repeat align_encoder_step.
      eapply CorrectAlignedEncoder_Projection2Compose.
      + intros. subst.
        eapply IsReorder_ID.
      + repeat align_encoder_step.
        * eapply CorrectAlignedEncoderForFormatSumType; simpl.
          constructor; [|constructor]; simpl; try now constructor.
          simpl. apply SimplPrimFst.
          align_encoder_step.
          simpl; apply SimplPrimFst.
          align_encoder_step.
    - (* synthesize_aligned_decoder. *)
      start_synthesizing_decoder.
      + normalize_format. (* apply_rules *)
        
        eapply sequence_Compose_format_decode_correct.
        { (*propagate cache invariant*)  eassumption. }
        { (* Actula format inside the compose*)
          unfold format_word_SumType, format_indexed_SumType.
          apply_rules.
          apply_rules.
          
          eapply SumType_decode_correct.
          Lemma replace_both_predicates
            S T
              (cache : Cache)
              (monoid : Monoid T)
              (decode_inv : CacheDecode -> Prop)
              view
              format
              decode
              view_format
              : Proper (pointwise_relation _ iff ==> impl)
                  (fun Predicate  =>
                   @CorrectDecoder S T cache S monoid Predicate Predicate
                                   view format decode decode_inv view_format).
          Proof.
            intros ??? HH. 
            eapply weaken_source_pred_Proper.
            { unfold impl, flip, pointwise_relation in *.
              intros. destruct (H a). apply (H2 H0). }
            eapply weaken_view_predicate; cycle 1.
            eassumption.
            { unfold impl, flip, pointwise_relation in *.
              intros. destruct (H a). eauto. }
          Qed.
          eapply replace_both_predicates; cycle 1.
          
          match goal with
          | |- context [CorrectDecoder _ _ _ _ (format_SumType (B := ?B) (cache := ?cache) (m := ?n) ?types _) _ _ _] =>
              idtac B cache n types;
              ilist_of_evar
                (fun T : Type => T -> @CacheFormat cache -> Comp (B * @CacheFormat cache)) types
                ltac:(fun formatrs' =>
                        ilist_of_evar
                          (fun T : Type => B -> @CacheDecode cache -> option (T * B * @CacheDecode cache)) types
                          ltac:(fun decoders' =>
                                  ilist_of_evar
                                    (fun T : Type => Ensembles.Ensemble T) types
                                    ltac:(fun invariants' =>
                                            ilist_of_evar
                                              (fun T : Type => T -> B -> Prop) types
                                              ltac:(fun invariants_rest' => 
                                                      Vector_of_evar n
                                                                     (Ensembles.Ensemble (CacheDecode -> Prop))
                                                                     ltac:(fun cache_invariants' =>
                                                                             eapply (SumType_decode_correct (m := n) types) with
                                                                             (formatrs := formatrs')
                                                                             (decoders := decoders')
                                                                             (invariants := invariants')
                                                                             (* (invariants_rest := invariants_rest') *)
                                                                             (cache_invariants :=  cache_invariants')
                                                                          )
                     ))))
          end.
          simpl.
          repeat (apply IterateBoundedIndex.Build_prim_and; intros); try exact I;
            apply_rules.
          - Transparent cache_inv_Property.
            revert H.
             unfold cache_inv_Property.
             intros.
            destruct H as [[] ?].
            repeat (apply IterateBoundedIndex.Build_prim_and; intros); try exact I; eauto.
          - (* IFF predicates *)
            intros ?; simpl; split.
            + intros [].
              split; try now 
                         eapply H3.
              unfold IsProj.
              unfold "∘".
              rewrite H2.
              Definition word2Fin' {sz} (w: word sz) (n:nat) (lt:wordToNat w < n) : Fin.t n.
                unshelve eapply Fin.of_nat_lt.
                - eapply wordToNat; eassumption.
                - assumption.
              Defined.
              Definition word2Fin {sz} (w: word sz) (n:nat) (lt:wordToNat w < n) :
                Fin.t n := Fin.of_nat_lt lt.
              Lemma roundTrip_word_fin: forall n sz (w: word sz)
                                      (lt:wordToNat w < n) , w = fin2Word _ (word2Fin w n lt).
              Proof.
                intros. unfold fin2Word, word2Fin.
                rewrite FinFun.Fin2Restrict.f2n_n2f, natToWord_wordToNat; reflexivity.
              Qed.
              erewrite (roundTrip_word_fin _ _ v1).
              shelve.
            + intros.
              split; cycle 1.
              * destruct a; simpl; auto.
              * destruct H2.
                apply IsProj_eq in H3.
                shelve.
        }
          
        { (*Propagate views*) clear H.
          simpl; intros.  split.
          instantiate(1:=2).
          unfold IsReorder in H0.
          - destruct v as [|v]; simpl in *; try discriminate.
            destruct v0 as [|v0]; simpl in *; try discriminate.
            destruct v1 as [|v1]; simpl in *; try discriminate.
            reflexivity.
          - intros. destruct x; eauto. }
            
        { (* extract_view: CorrectDecoder of empty_Format *)
          (*ExtractSource*)
            Definition pure_invertion (ls : list (SumType.SumType [word 8 : Type; word 16 : Type])):
            sensor_msg:=
            match invert_reordering ls with
              Some s => s
            | None => (*Default*) Build_sensor_msg (wzero _) (wzero _)
            end.
            simpl; intros.
            unshelve eapply CorrectDecoderEmpty.
            2:{ eapply pure_invertion; eauto. }
            shelve.

            
          2:{ unfold Tuple.GetAttribute, Tuple.GetAttributeRaw, IsProj in *; simpl in *; intros.
              intuition.
              eapply decides_and.
              2:{ unfold IsReorder.
                  unshelve eapply decides_dec_eq; auto using Nat.eq_dec, weq, pair_eq_dec.
                  exact (fun a b =>
                           match a, b with
                           | Some (Build_sensor_msg id1 data1), 
                             Some (Build_sensor_msg id2 data2) => (andb (weqb id1 id2) (weqb data1 data2))
                           | None, None => true
                           | _, _ => false
                           end
                        ).
                  intros.
                  split.
                  -  intros; subst. destruct a'; auto.
                     destruct s; auto using Nat.eq_dec, weq, pair_eq_dec.
                     apply andb_true_intro; split; apply weqb_true_iff; reflexivity.
                  - intros HH. destruct a, a'; auto; try discriminate.
                    + destruct s, s0; auto; try discriminate.
                      symmetry in HH; apply Bool.andb_true_eq in HH. destruct HH.
                      symmetry in H1, H4.
                      eapply weqb_true_iff in H1, H4; subst; auto.
                    + destruct s; discriminate. }
              unfold invariant.
              instantiate(1:= true); constructor. }
          - (* build_fully_determined_type. *)
            decompose_source_predicate.
            unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw,
              Basics.compose in *; simpl in *.
            let a' := fresh in
            intros a'; try destruct a'. destruct_conjs.
            unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw
              in *; simpl in *. intros.
            decompose_source_predicate.
            unfold IsReorder in *.
            subst_projections.
            unfold pure_invertion.
            rewrite H3. reflexivity. }

      + (* synthesize_cache_invariant.*)
        repeat instantiate ( 1 := (constant True) ).
        repeat (first [ apply unfold_cache_inv_Property | intuition ]).
        simpl.
        unfold Vector.nth; simpl. constructor.
      + cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
      + (* align_decoders_step *) cbv beta.
        align_decoders_step.
        let T:=type of types in idtac T.
        (* Make the ilist vars and then apply align_decoders_step*)
        let types' := eval unfold types in types in
          ilist_of_evar
            (fun T : Type =>
               ByteString ->
               CacheDecode ->
                option (T * ByteString * CacheDecode))
            types'
            ltac:(fun decoders =>
                    ilist_of_evar
                      (fun T : Type =>
                         forall n : nat,
                           @AlignedDecodeM test_cache T n)
                      types'
                      ltac:(fun aligned_decoders =>
                              eapply (@AlignedDecodeSumTypeM
                                        _ _ _ types' decoders aligned_decoders
                                     )
                           )
                 ).
        simpl.
        apply IterateBoundedIndex.Build_prim_and; intros.
        eapply DecodeMEquivAlignedDecodeM_trans; cycle 1.
        intros; symmetry; cbv beta; simpl;
            unfold decode_nat, sequence_Decode. optimize_decoder_impl. }
        simpl; intros. higher_order_reflexivity. } 
           | try exact I ]
        * simpl. 

          eapply DecodeMEquivAlignedDecodeM_trans.
            2: { intros; simpl; reflexivity. }
            1: eapply AlignedDecode_ifopt; intros.
            2: { intros; simpl. reflexivity.
           | intros; higher_order_reflexivity ]; intros.

        eapply AlignedDecode_CollapseWord'.
        eapply AlignedDecode_ifopt.
         
        
  Defined.

  
  Let encode := encoder_impl enc_dec.
  
  Let decode := decoder_impl enc_dec.
  
      
        Definition CorrectAlignedEncoderIlist n {types C}
                   (formats: ilist.ilist(B:=fun S => @FormatM S ByteString C) types)
                   (encoders: ilist.ilist(B:=fun S => forall sz : nat, @AlignedEncodeM C S sz) types):=
          forall idx : Fin.t n,
            CorrectAlignedEncoder (ilist.ith formats idx)
                                  (ilist.ith encoders idx).
         Lemma CorrectAlignedEncoderIlistBase:
          forall types C
            (formats: ilist.ilist(B:=fun S => @FormatM S ByteString C) types)
            (encoders: ilist.ilist(B:=fun S => forall sz : nat, @AlignedEncodeM C S sz) types),
            CorrectAlignedEncoderIlist 0 formats encoders.
        Proof. intros ** idx; inversion idx. Qed. 

        Lemma CorrectAlignedEncoderIlistStep:
          forall T__n (C : Cache)
            (format__n: FormatM T__n ByteString)
            encoder__n,
            @CorrectAlignedEncoder C T__n format__n encoder__n ->
            forall (n : nat) (types : t Type n) (C : Cache)
              (formats encoders : ilist.ilist types),
              CorrectAlignedEncoderIlist n formats encoders->
              CorrectAlignedEncoderIlist
                (S n)
                ((Build_prim_prod format__n formats):(ilist (Vector.cons _ T__n _ types))) 
                (Build_prim_prod encoder__n encoders).
        Proof.
          intros ** idx.
          dependent destruction idx.
          - simpl. eauto.
          - simpl. eapply X0.
        Qed.
        
      

End ReorderTest
*)


Module Sensor0.
  Record sensor_msg :=
    { stationID: word 8; data: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.
  Ltac apply_rules' :=
          first
            [ extract_view; idtac "0"
            | apply_base_rule; idtac "1"
            | apply_combinator_rule ltac:(apply_rules')
            | idtac; idtac "3" ].
  Ltac apply_rules'' :=
          idtac "applying rules 2";
          first
            [ apply_base_rule; idtac "1"
            | apply_combinator_rule ltac:(apply_rules'')
            | idtac; idtac "3" ].

  
  Let enc_dec : EncoderDecoderPair format invariant.
  Proof.
    econstructor.
    - synthesize_aligned_encoder.
    - (* synthesize_aligned_decoder *)
      start_synthesizing_decoder.
      + normalize_format.
        progress apply_combinator_rule ltac:(apply_rules'').
        (*extract_view.*)
        (*ExtractSource.*)
        simpl; intros; eapply CorrectDecoderEmpty.
        * (*build_fully_determined_type.*)
          unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw, Basics.compose
            in *; simpl in *.
          let a' := fresh in
          intros a'; try destruct a'; destruct_conjs.
          unfold Heading.Domain, Tuple.GetAttribute, Tuple.GetAttributeRaw in *; 
            simpl in *; intros.
          decompose_source_predicate.
          subst_projections. reflexivity.
            
        * decide_data_invariant.

      (* apply_rules'
         2 1 2 2 1 2 0*)
        apply_rules''.
        simpl; intros. eapply CorrectDecoderEmpty.
        build_fully_determined_type.
        decide_data_invariant.
        ExtractSource.
        extract_view. 
        apply_combinator_rule.
        apply_base_rule.
          
      + cbv beta; synthesize_cache_invariant. 
      + cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
      + cbv beta.
        align_decoders_step.
      *)
      
       (* derive_encoder_decoder_pair. *)

  Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
     (stationID ⋙ SetCurrentByte ≫
      data ⋙ (low_bits 8 ⋙ SetCurrentByte ≫
      shift_right 8 ⋙ SetCurrentByte)) v 0 r tt *)
  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b0⋅b';
      return {| stationID := b; data := w |}) v 0 tt *)
End ReorderTest.

(** All user input is contained in box 1. `sensor_msg` is a record type with two fields; the Coq `Record` command additionally defines two functions `stationID` and `data` (of type `sensor_msg → …`) to access these fields. `format` specifies how to encode instances of this record: `format_word` is a Narcissus primitive that writes out its input bit by bit, and `++` is a sequencing operator (write this, then that).  `invariant` specifies additional constraints on well-formed packets, but there are none here.  Box 2 calls the `derive_encoder_decoder_pair` tactic provided by Narcissus, which generates an encoder and a decoder along with proofs of correctness (it takes about two to five seconds to return); the rest is routine boilerplate.  Boxes 2 and 3 show generated code. In box 2, the generated encoder takes a packet and a byte buffer and returns the encoded packet or `None` if it did not fit in the supplied buffer. In box 3, the decoder takes a buffer, and returns a packet or None if the buffer did not contain a valid encoding. Both generated programs live in stateful error monads, offering primitives to read (GetCurrentByte), skip (SkipCurrentByte), and write (SetCurrentByte) a single byte.  The encoder uses `low_bits` and `shift_right` to extract the low and high bits of the `data` field, and the decoder reassembles these two bytes using a shift and an addition, using the `⋅` operator: this byte-alignment transformation is part of the `derive_encoder_decoder_pair` logic. **)

(** We now introduce a twist: to preserve 16-bit alignment, we introduce 8 bits of padding after encoding `stationID`; these bits will be reserved for future use. **)

Module Sensor1.
  Record sensor_msg :=
    { stationID: word 8; data: word 16 }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : t Core.char sz) =>
    (stationID ⋙ SetCurrentByte ≫
     const WO~0~0~0~0~0~0~0~0 ⋙ SetCurrentByte ≫
     data ⋙ (low_bits 8 ⋙ SetCurrentByte ≫
             shift_right 8 ⋙ SetCurrentByte)) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : t Core.char sz) =>
     (b <- GetCurrentByte;
      _ <- SkipCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      return {| stationID := b; data := w |}) v 0 tt *)
End Sensor1.

(** Notice the asymmetry that these 8 under-specified bits introduce: although the encoder always writes `0x00`, the decoder accepts any value.  This is crucial because the `format_unused_word` specification allows conforming encoders to output any 8-bits value; as a result, the decoder must accept all 8-bit values.  In that sense, the encoder and decoder that Narcissus generates are not inverse of each other: the encoder is one among a family of functions permitted by the formatting specification, and the decoder is the inverse of the *entire family*, accepting any output produced by a conforming encoder. **)

(** Our next enhancement is to introduce a version number field in our packet, and to tag each measurement with a `kind`, `"TEMPERATURE"` or `"HUMIDITY"`.  To save space, we allocate 2 bits for the `kind` tag, and 14 bits to the actual measurement. **)

(* The rules for higher-order types (lists, sums, sequences. *)
Module Sensor2.

  Let kind :=
      EnumType ["TEMPERATURE"; "HUMIDITY"].

  Record sensor_msg :=
    { stationID: word 8; data: (kind * word 14) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_enum [WO~0~0; WO~0~1] ◦ fst ◦ data
    ++ format_word ◦ snd ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.  Defined.

  Let encode := encoder_impl enc_dec.
  (* (stationID ▹ SetCurrentByte ≫
     const WO~0~0~0~0~0~0~0~0 ▹ SetCurrentByte ≫
     const WO~0~0~0~0~0~1~1~1 ▹ SetCurrentByte ≫
     const WO~1~1~1~0~0~0~1~0 ▹ SetCurrentByte ≫
     (fun (v4 : ByteBuffer.t sz) (idx4 : nat) (r4 : sensor_msg) =>
      (low_bits 8 ▹ SetCurrentByte ≫
       shift_right 8 ▹ SetCurrentByte) v4 idx4 (Word.combine ((snd ∘ data) r4) ((Vector.nth [WO~0~0; WO~0~1] ∘ (fst ∘ data)) r4)))) v
  0 r tt *)
  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : ByteBuffer.t sz) =>
     (b <- GetCurrentByte;
     _ <- GetCurrentByte;
     b1 <- GetCurrentByte;
     b' <- GetCurrentByte;
     w <- return b1⋅b';
     (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
     then
        b2 <- GetCurrentByte;
        b'0 <- GetCurrentByte;
        w0 <- return b2⋅b'0;
        Ifopt if weqb (split2 14 2 w0) WO~0~0
        then Some Fin.F1
        else
        match (if weqb (split2 14 2 w0) WO~0~1 then Some Fin.F1 else None) with
          | Some f => Some (Fin.FS f)
          | None => None
          end as a' Then return {| stationID := b; data := (a', split1 14 2 w0) |} Else fail
  else fail)) v 0 tt *)
End Sensor2.

(** The use of `format_const _` in the specification forces conforming encoders must write out the value 0x7e2, encoded over 16 bits.  Accordingly, the generated decoder throws an exception if its input does not contain that exact sequence.  The argument passed to `format_enum` specifies which bit patterns to use to represent each tag (`0b00` for `"TEMPERATURE"`, `0b01` for `"HUMIDITY"`), and the decoder uses this mapping to reconstruct the appropriate enum member. **)

(** We use the next iteration to illustrate data dependencies and input restrictions.  To do so, we replace our single data point with a list of measurements (for conciseness, we remove tags and use 16-bit words).  We start as before, but we quickly run into an issue : **)

Module Sensor3.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof.
    derive_encoder_decoder_pair.
    last_failing_goal.
    all:simpl.
  Abort.
End Sensor3.

(** The derivation fails, leaving multiple Coq goals unsolved.  We forgot to encode the length of the `data` list, and this prevents Narcissus from generating a decoder.  Our attempted fix, unfortunately, only gets us half of the way there (`format_nat 8 ◦ length` specifies that the length of the list should be truncated to 8 bits and written out): **)

Module Sensor4.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant (msg: sensor_msg) :=
    True.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
         last_failing_goal.
         all:simpl.
  Abort.
End Sensor4.

(** Again, decoder generation fails and produces an unsolvable goal. The problem is that, since we encode the list's length on 8 bits, the round-trip property that Narcissus attempts to prove only holds if the list has less than \(2^{8}\) elements: larger lists have their length truncated, and it becomes impossible for the decoder to know for cetain how many elements it should decode.  What we need is an input restriction: a predicate defining which messages we may encode; to this end, we update our example as follows:
**)

Module Sensor5.
  Record sensor_msg :=
    { stationID: word 8; data: list (word 16) }.

  Let format :=
       format_word ◦ stationID
    ++ format_nat 8 ◦ length ◦ data
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_list format_word ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

        Ltac apply_rules' :=
          idtac "applying rules 2";
          first
            [ extract_view; idtac "0"
            | apply_base_rule; idtac "1"
            | apply_combinator_rule ltac:(apply_rules')
            | idtac; idtac "3" ].
  Let enc_dec : EncoderDecoderPair format invariant.
  Proof.
    econstructor; [ synthesize_aligned_encoder |  ].
    (*Decoder*)
    - start_synthesizing_decoder.
      + normalize_format. apply_rules'.
      + cbv beta; synthesize_cache_invariant. 
      + cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
      + cbv beta.
        align_decoders_step.
        align_decoders_step.
        align_decoders_step.
        eapply @AlignedDecodeListM; intros; eauto.
        match goal with
        | [  |- ?f _ ?evar ] => cut (evar = evar) 
        end.
        intros.
        align_decoders_step.
        align_decoders_step.

        align_decoders.
        ltac:()
   ltac:()
   ltac:()
   ltac:() ltac:(continue_on_fail_2)
   ltac:(continue_on_fail_1) ltac:(continue_on_fail)
    synthesize_aligned_decoder.
    
    
    derive_encoder_decoder_pair. Defined.

  Let encode := encoder_impl enc_dec.
  (* fun (sz : nat) (r : sensor_msg) (v : ByteBuffer.t sz) =>
     (stationID ⋙ SetCurrentByte ≫
      data ⋙ Datatypes.length ⋙ natToWord 8 ⋙ SetCurrentByte ≫
      const WO~0~0~0~0~0~1~1~1 ⋙ SetCurrentByte ≫
      const WO~1~1~1~0~0~0~1~0 ⋙ SetCurrentByte ≫
      data ⋙ AlignedEncodeList (fun n : nat => low_bits 8 ⋙ SetCurrentByte ≫
                                               shift_right 8 ⋙ SetCurrentByte) sz) v 0 r tt *)

  Let decode := decoder_impl enc_dec.
  (* fun (sz : nat) (v : ByteBuffer.t sz) =>
     (b <- GetCurrentByte;
      b0 <- GetCurrentByte;
      b1 <- GetCurrentByte;
      b' <- GetCurrentByte;
      w <- return b1⋅b';
      (if weq w WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
       then
        l <- ListAlignedDecodeM
               (fun numBytes : nat =>
                w0 <- GetCurrentByte;
                w' <- w1 <- GetCurrentByte;
                      w' <- return WO;
                      return w1⋅w';
                return w0⋅w') (wordToNat b0);
        return {| stationID := b; data := l |}
       else fail)) v 0 tt *)
End Sensor5.

Module Sensor6.

  Inductive reading :=
  | Temperature (_ : word 14)
  | Humidity (_ : word 14).

  Let format_reading m s :=
    match m with
    | Temperature t => ret (serialize (Word.combine WO~0~0 t) s)
    | Humidity h => ret (serialize (Word.combine WO~0~1 h) s)
    end.

  Let enc_reading sz :=
    (fun buf idx m => @SetCurrentBytes _ _ sz 2 buf idx match m with
         | Temperature t => Word.combine WO~0~0 t
         | Humidity h => Word.combine WO~0~1 h
         end).

  Lemma enc_readingCorrect
    : CorrectAlignedEncoder format_reading enc_reading.
  Proof.
    unfold enc_reading, format_reading.
    eapply refine_CorrectAlignedEncoder.
    2: eapply CorrectAlignedEncoderForFormatMChar_f; eauto.
    intros; destruct s; simpl;
      rewrite refine_Projection_Format;
      split; try reflexivity;
        intros; eapply format_word_inhabited'; intros; eauto.
  Qed.

  Let dec_reading :=
    fun t ctx =>
    `(w, rest, ctx') <- decode_word t ctx;
      if weqb (split1 2 14 w) WO~0~0
      then Some (Temperature (split2 2 14 w), rest, ctx')
      else (if weqb (split1 2 14 w) WO~0~1 then
              Some (Humidity (split2 2 14 w), rest, ctx')
            else None).

  Transparent weqb.

  Lemma dec_readingCorrect
    : CorrectDecoder _ (fun _ => True) (fun _ => True) eq format_reading dec_reading (fun _ => True)
                     format_reading.
  Proof.
    eapply format_decode_correct_EquivFormatAndView
        with (fun m => format_word (match m with
                                 | Temperature t => Word.combine WO~0~0 t
                                 | Humidity h => Word.combine WO~0~1 h
                                 end)); eauto.
    unfold flip, EquivFormat, format_reading. intros; destruct s; reflexivity.

    apply_bijection_rule' with (fun w =>
                                  if weqb (split1 2 14 w) WO~0~0
                                  then Some (Temperature (split2 2 14 w))
                                  else (if weqb (split1 2 14 w) WO~0~1 then
                                          Some (Humidity (split2 2 14 w))
                                        else None));
      intuition eauto.
    - apply Word_decode_correct. try apply unfold_cache_inv_Property; intuition eauto.
    - destruct s; simpl; rewrite split2_combine; auto.
    - destruct weqb eqn:?; injections. apply weqb_true_iff in Heqb.
      rewrite <- Heqb. apply Word.combine_split.
      destruct (weqb _ WO~0~1) eqn:?; try discriminate; injections. apply weqb_true_iff in Heqb0.
      rewrite <- Heqb0. apply Word.combine_split.
    - intuition eauto.
    - derive_decoder_equiv; easy.
  Qed.

  Opaque weqb.
  Record sensor_msg :=
    { stationID: word 8; data: list reading }.

  Let format :=
       format_word ◦ stationID
    ++ format_unused_word 8
    ++ format_const WO~0~0~0~0~0~1~1~1~1~1~1~0~0~0~1~0
    ++ format_nat 8 ◦ length ◦ data
    ++ format_list format_reading ◦ data.

  Let invariant :=
    fun (msg: sensor_msg) =>
      length (msg.(data)) < pow2 8.

  Ltac new_encoder_rules ::= apply enc_readingCorrect.
  Ltac apply_new_base_rule ::= apply dec_readingCorrect.

  Let enc_dec : EncoderDecoderPair format invariant.
  Proof. derive_encoder_decoder_pair.
  Defined.

  Let encode := encoder_impl enc_dec.
  Let decode := decoder_impl enc_dec.

End Sensor6.
