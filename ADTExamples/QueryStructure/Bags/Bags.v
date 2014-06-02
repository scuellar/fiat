Require Import Program.
Require Import FMapInterface.
Require Import FMapAVL OrderedTypeEx.
Require Import Coq.FSets.FMapFacts.
Require Import FMapExtensions.

Unset Implicit Arguments.

Definition flatten {A} :=
  @List.fold_right (list A) (list A) (@List.app A) [].

Lemma in_flatten_iff :
  forall {A} x seqs, 
    @List.In A x (flatten seqs) <-> 
    exists seq, List.In seq seqs /\ List.In x seq.
Proof.
  intros; unfold flatten.
  induction seqs; simpl. 

  firstorder.
  rewrite in_app_iff.
  rewrite IHseqs.

  split.
  intros [ in_head | [seq (in_seqs & in_seq) ] ]; eauto.
  intros [ seq ( [ eq_head | in_seqs ] & in_seq ) ]; subst; eauto.
Qed.

Class Bag (TContainer TItem TSearchTerm: Type) :=
  {
    bempty     : TContainer;
    benumerate : TContainer -> list TItem;
    bfind      : TContainer -> TSearchTerm -> list TItem;
    binsert    : TContainer -> TItem -> TContainer;
    
    binsert_enumerate : forall item inserted container,
                          List.In item (benumerate (binsert container inserted)) <->
                          List.In item (benumerate container) \/ item = inserted;
    benumerate_empty  : forall item, ~ List.In item (benumerate bempty)
  }.

Module IndexedTree (Import M: WS).
  Module Import BasicFacts := WFacts_fun E M.
  Module Import BasicProperties := WProperties_fun E M.
  Module Import MoreFacts := FMapExtensions_fun E M.

  Definition TKey := key.

  Definition IndexedBagConsistency 
             {TBag TItem TBagSearchTerm: Type}
             {bags_bag: Bag TBag TItem TBagSearchTerm}
             projection fmap :=
    forall (key: TKey) (bag: TBag),
      MapsTo key bag fmap -> 
      forall (item: TItem),
        List.In item (benumerate bag) ->
        E.eq (projection item) key.

  Record IndexedBag 
         {TBag TItem TBagSearchTerm: Type} 
         {bags_bag: Bag TBag TItem TBagSearchTerm} 
         {projection} :=
    { 
      ifmap        : t TBag;
      iconsistency : IndexedBagConsistency projection ifmap
    }.

  Definition EmptyAsIndexedBag 
             (TBag TItem TBagSearchTerm: Type) 
             (bags_bag: Bag TBag TItem TBagSearchTerm) projection 
  : @IndexedBag TBag TItem TBagSearchTerm bags_bag projection.
    refine (
        {|
          ifmap        := empty TBag;
          iconsistency := _
        |}
      ).
    Proof. 
      unfold IndexedBagConsistency; 
      intros; rewrite empty_mapsto_iff in *; exfalso; trivial.
    Defined.

    Definition FindWithDefault {A} (key: TKey) (default: A) (fmap: t A) :=
      match find key fmap with
        | Some result => result
        | None        => default
      end.

    Definition Values {A} container :=
      List.map snd (@elements A container).

    Lemma consistency_key_eq :
      forall {TBag TItem TBagSearchTerm},
      forall bags_bag (projection: TItem -> TKey),
      forall (indexed_bag: @IndexedBag TBag TItem TBagSearchTerm bags_bag projection),
      forall (key: TKey) bag item,
        MapsTo key bag (ifmap indexed_bag) ->
        List.In item (benumerate bag) ->
        E.eq (projection item) key.
    Proof.
      intros.
      destruct indexed_bag as [? consistent].
      unfold IndexedBagConsistency in consistent.
      eapply consistent; eauto.
    Qed.      

    Lemma FindWithDefault_dec :
      forall {A : Type} (key : TKey) (default : A) (fmap : t A),
        { exists result, 
            MapsTo key result fmap /\
            @FindWithDefault A key default fmap = result } +
        { find key fmap = None /\ 
          @FindWithDefault A key default fmap = default }.
    Proof.
      unfold FindWithDefault;
      intros A key default fmap; 
      destruct (find key fmap) eqn:find;
      [ left; rewrite <- find_mapsto_iff in find | right ];
      eauto.
    Qed.

    Lemma Values_empty :
      forall {A}, Values (empty A) = []. 
    Proof.
      intros;
      unfold Values;
      rewrite elements_empty;
      reflexivity.
    Qed.

    Instance IndexedBagAsBag 
             (TBag TItem TBagSearchTerm: Type) 
             (bags_bag: Bag TBag TItem TBagSearchTerm) projection 
    : Bag 
        (@IndexedBag TBag TItem TBagSearchTerm bags_bag projection) 
        TItem 
        ((option TKey) * TBagSearchTerm) :=
      {| 
        bempty := 
          EmptyAsIndexedBag TBag TItem TBagSearchTerm bags_bag projection;

        benumerate container :=
          flatten (List.map benumerate (Values (container.(ifmap))));

        bfind container key_searchterm :=
          let (key_option, search_term) := key_searchterm in
          match key_option with
            | Some k =>
              match find k container.(ifmap) with
                | Some bag => bag.(bfind) search_term
                | None     => []
              end
            | None   =>
              flatten (List.map (fun bag => bag.(bfind) search_term) (Values container.(ifmap)))
          end;

        binsert container item :=
          let k := projection item in
          let bag := FindWithDefault k bempty container.(ifmap) in
          {|
            ifmap := add k (bag.(binsert) item) container.(ifmap);
            iconsistency := _
          |};

        binsert_enumerate := _
      |}.
    Proof.
      intros; simpl in *.

      unfold Values.
      setoid_rewrite in_flatten_iff.
      setoid_rewrite in_map_iff.
      setoid_rewrite <- MapsTo_snd.

      split; intro H.
      
      destruct H as [ items ( [ bag (bag_items & [ key maps_to ]) ] & in_seq ) ].
      pose proof maps_to as maps_to'.
      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)].

      subst.
      rewrite binsert_enumerate in in_seq.
      destruct in_seq as [ in_seq | ? ]; eauto.
      left.
      
      Ltac autoexists :=
        repeat progress match goal with
                          | [ |- exists _, _ ] => eexists; autoexists
                          | [ |- ?a = ?b ]     => first [ (has_evar a; has_evar b; idtac) | eauto]
                          | [ |- E.eq _ _ ]    => eauto
                          | [ |- _ /\ _ ]      => split; autoexists
                          | [ |- _ \/ _ ]      => left; autoexists
                        end.
      
      destruct (FindWithDefault_dec (projection inserted) bempty (ifmap container)) 
        as [ [result (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.
      
      autoexists; eauto.
      
      exfalso; apply benumerate_empty in in_seq; tauto.

      autoexists; eauto.

      Focus 2.
      unfold flatten, EmptyAsIndexedBag; simpl.
      rewrite Values_empty; tauto.

      destruct H as [ [ items ( [ bag ( bag_items & [ key maps_to ] ) ] ) ] | eq_item_inserted ].
      
      pose proof maps_to as maps_to'.
      apply (iconsistency container) in maps_to.    
      setoid_rewrite bag_items in maps_to.
      specialize (maps_to item H).
      
      setoid_rewrite add_mapsto_iff.

      destruct (E.eq_dec (projection inserted) key);
        try solve [ repeat (eexists; split; eauto) ].
      
      autoexists.

      apply binsert_enumerate.

      destruct (FindWithDefault_dec (projection inserted) bempty (ifmap container))
        as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.

      rewrite e in mapsto.
      pose proof (MapsTo_fun mapsto maps_to') as bag'_bag.
      rewrite bag'_bag.
      rewrite bag_items.
      auto.

      rewrite find_mapsto_iff in maps_to'.
      rewrite <- e in maps_to'.
      match goal with 
        | [ H: ?a = Some ?b, H': ?a = None |- _ ] => assert (Some b = None) by (transitivity a; auto); discriminate
      end.

      subst item.
      match goal with
        | [ |- context [ add ?key ?value ?container ] ] => set (k := key); set (v := value)
      end.

      exists (benumerate v).
      split.
      exists v; split; trivial.
      exists k.

      apply add_1; trivial.
      unfold v.
      rewrite binsert_enumerate; auto.

      Grab Existential Variables.
      intros k' bag' maps_to item'.

      rewrite add_mapsto_iff in maps_to;
        destruct maps_to as [(is_eq & refreshed) | (neq & maps_to)];
        subst.

      rewrite binsert_enumerate.
      intro H; destruct H.
      apply (iconsistency container k' bag); trivial.    

      rewrite <- is_eq.
      unfold bag in *.

      destruct (FindWithDefault_dec k bempty (ifmap container))
        as [ [bag' (mapsto & equality)] | (not_found & equality) ];
        rewrite equality in *; clear equality.

      subst; trivial.
      exfalso; apply benumerate_empty in H; trivial.
      
      subst.
      unfold k in *. 
      trivial.

      apply (iconsistency container k' bag' maps_to item').
    Defined.

    Print Assumptions IndexedBagAsBag. 
End IndexedTree.

Instance ListAsBag
         {TItem TSearchTerm: Type}
         (matcher: TSearchTerm -> TItem -> bool)
: Bag (list TItem) TItem TSearchTerm.
Proof.
  refine (
      {| 
        bempty := []; 
        benumerate := id;
        bfind container search_term := List.filter (matcher search_term) container;
        binsert container item := cons item container
      |}
    ); simpl in *; intuition.
Defined.

Require Import Tuple Heading.

Definition TSearchTermMatcher (heading: Heading) := (@Tuple heading -> bool).

Definition SearchTermsCollection heading :=
  list (TSearchTermMatcher heading).

Fixpoint MatchAgainstSearchTerms 
         {heading: Heading}
         (search_terms : SearchTermsCollection heading) (item: Tuple) :=
  match search_terms with
    | []                     => true
    | is_match :: more_terms => (is_match item) && MatchAgainstSearchTerms more_terms item
  end.

Definition HasDecidableEquality (T: Type) :=
  forall (x y: T), {x = y} + {x <> y}.

Definition TupleEqualityMatcher 
           {heading: Heading} 
           (attr: Attributes heading)
           (value: Domain heading attr) 
           {eq_dec: HasDecidableEquality (Domain heading attr)} : TSearchTermMatcher heading :=
  fun tuple => 
    match eq_dec (tuple attr) value with
      | in_left  => true
      | in_right => false
    end.

Instance TupleListAsBag (heading: Heading) :
  Bag (list (@Tuple heading)) (@Tuple heading) (SearchTermsCollection heading).
Proof.
  apply (ListAsBag (@MatchAgainstSearchTerms heading)).
Defined.

Require Import Beatles.
Require Import StringBound.
Require Import Peano_dec.
Require Import String_as_OT.

Open Scope string_scope.
Open Scope Tuple_scope.

Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := string_dec) Name "Please Please Me" ]).

Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := eq_nat_dec) Year 3]).

Eval simpl in (bfind FirstAlbums [ TupleEqualityMatcher (eq_dec := eq_nat_dec) Year 3; TupleEqualityMatcher (eq_dec := eq_nat_dec) UKpeak 1]).

Module NatIndexedMap := FMapAVL.Make Nat_as_OT.
Module StringIndexedMap := FMapAVL.Make String_as_OT.

Module NatTreeExts := IndexedTree NatIndexedMap.
Module StringTreeExts := IndexedTree StringIndexedMap.

Definition NatTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@NatTreeExts.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm 
     subtree_as_bag).

Definition StringTreeType TSubtree TSubtreeSearchTerm heading subtree_as_bag := 
  (@StringTreeExts.IndexedBag 
     TSubtree 
     (@Tuple heading) 
     TSubtreeSearchTerm
     subtree_as_bag).

Definition cast {T1 T2: Type} (eq: T1 = T2) (x: T1) : T2.
Proof.
  subst; auto.
Defined.

Record BagPlusBagProof heading :=
  { BagType: Type; SearchTermType: Type; BagProof: Bag BagType (@Tuple heading) SearchTermType }.

Record ProperAttribute {heading} :=
  {
    Attribute: Attributes heading; 
    ProperlyTyped: { Domain heading Attribute = nat } + { Domain heading Attribute = string }
  }.

Fixpoint NestedTreeFromAttributes'
         heading 
         (indexes: list (@ProperAttribute heading)) 
         {struct indexes}: BagPlusBagProof heading :=
  match indexes with
    | [] => 
      {| BagType        := list (@Tuple heading);
         SearchTermType := SearchTermsCollection heading |}
    | proper_attr :: more_indexes => 
      let attr := Attribute proper_attr in
      let (t, st, bagproof) := NestedTreeFromAttributes' heading more_indexes in
      match (ProperlyTyped proper_attr) with
        | left eq_nat     => 
          {| BagType        := NatTreeType t st heading bagproof (fun x => cast eq_nat x!attr);
             SearchTermType := option nat * st |}
        | right eq_string => 
          {| BagType        := StringTreeType t st heading bagproof (fun x => cast eq_string x!attr);
             SearchTermType := option string * st |}
      end
    end.

Lemma eq_attributes : forall seq (a b: @BoundedString seq),
             a = b <-> (bindex a = bindex b /\ (ibound (indexb a)) = (ibound (indexb b))).
  split; intros; 
  simpl in *;
  try (subst; tauto);
  apply idx_ibound_eq; 
    intuition (apply string_dec).
Qed.

Ltac ProveDecidability indices :=
  refine (NestedTreeFromAttributes' AlbumHeading indices _);
  intros attr in_indices; simpl in *;
  setoid_rewrite eq_attributes in in_indices;

  destruct attr as [bindex indexb];
  destruct indexb as [ibound boundi];
  simpl in *;

  repeat match goal with 
           | [ |- _ ] => 
             destruct ibound as [ | ibound ];
               [ try (exfalso; omega); solve [eauto] | try discriminate ]
         end.

Definition CheckType {heading} (attr: Attributes heading) (rightT: _) :=
  {| Attribute := attr; ProperlyTyped := rightT |}.

Ltac autoconvert func :=
  match goal with 
    | [ src := cons ?head ?tail |- list _ ] =>
      refine (func head _ :: _);
        [ solve [ eauto with * ] | clear src;
                            set (src := tail);
                            autoconvert func ]
    | [ src := nil |- list _ ] => apply []
    | _ => idtac
  end.

Ltac mkIndex heading attributes :=
  set (source := attributes);
  assert (list (@ProperAttribute heading)) as decorated_source;
  autoconvert (@CheckType heading);
  apply (NestedTreeFromAttributes' AlbumHeading decorated_source).

Definition SampleIndex : BagPlusBagProof AlbumHeading.
Proof.
  mkIndex AlbumHeading [Year; UKpeak; Name].
Defined.

Definition SampleIndex' : BagPlusBagProof AlbumHeading.
Proof.
  refine (NestedTreeFromAttributes' AlbumHeading [CheckType Year _; CheckType UKpeak _; CheckType Name _]);   eauto.
Defined.

Definition IndexedAlbums :=
  List.fold_left binsert FirstAlbums (@bempty _ _ _ (BagProof _ SampleIndex)).

Eval simpl in (SearchTermType AlbumHeading SampleIndex).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (None, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (None, [])))).
Time Eval simpl in (bfind IndexedAlbums (Some 3, (Some 1, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (Some "With the Beatles", [])))).
Time Eval simpl in (bfind IndexedAlbums (None, (None, (None, [TupleEqualityMatcher (eq_dec := string_dec) Name "With the Beatles"])))).

(*Time Eval simpl in (@bfind _ _ _ (BagProof _ SampleIndex) IndexedAlbums (Some 3, (Some 1, (None, @nil (TSearchTermMatcher AlbumHeading))))).*)

(*
  simpl.
  unfold bfind.
  unfold IndexedAlbums.
  unfold BagProof.
  unfold SampleIndex.
  unfold NestedTreeFromAttributes'.
  unfold right_type.
  unfold CheckType.
  unfold bempty.
  simpl attribute.
  unfold StringTreeType.
  unfold NatTreeType.
  unfold fold_left.
  unfold FirstAlbums.
  progress simpl NatTreeExts.IndexedBagAsBag.
  (*progress simpl StringTreeExts.IndexedBagAsBag.*)
  unfold NatTreeExts.IndexedBagAsBag.
  simpl.
*)
