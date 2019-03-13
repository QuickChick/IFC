Require Import Datatypes.
Require Import ZArith.
Require Import Coq.Strings.String.

From QuickChick Require Import QuickChick.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

Require Import Utils Labels.
Import LabelEqType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* I'm ending the craziness. Label model is now fixed to be Lab4. *)
Inductive alloc_mode := Global | Local.

Inductive frame A := Fr (lab : Label) : seq A -> frame A.

Section FrameEqType.

Variables A : eqType.

Definition frame_eq (fr1 fr2 : @frame A) : bool :=
  let: Fr l1 xs1 := fr1 in
  let: Fr l2 xs2 := fr2 in
  [&& l1 == l2 & xs1 == xs2].

Lemma frame_eqP : Equality.axiom frame_eq.
Proof.
move=> [l1 xs1] [l2 xs2]; apply/(iffP andP).
  by move=> [/eqP -> /eqP ->].
by move => [-> ->]; rewrite !eqxx.
Qed.

Definition frame_eqMixin := EqMixin frame_eqP.

Canonical frame_eqType := Eval hnf in EqType (frame A) frame_eqMixin.

End FrameEqType.

Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.DecidableTypeEx.
From QuickChick Require Import FMapWeakListInstances.
Require Import Coq.FSets.FMapFacts.

Module Lab_as_MDT <: MiniDecidableType.
  Definition t := Label.
  Definition eq_dec : forall x y : t, {x=y}+{~x=y}.
  Proof. decide equality. Defined.
End Lab_as_MDT.

Module Lab_as_UDT := Make_UDT(Lab_as_MDT).
  
Definition block := (Z * Lab_as_UDT.t)%type.

Definition block_eq (b1 b2 : block) := b1 == b2.

Lemma block_eqP : Equality.axiom block_eq.
Proof. move=> ??; exact/eqP. Defined.

Definition block_eqMixin := EqMixin block_eqP.
Canonical block_eqType := EqType block block_eqMixin.

Definition stamp : block -> Label := @snd _ _.
Definition put_stamp (s : Label) (b : block) : block :=
    let (z,_) := b in (z,s).

(* Memory is just a map from stamps to lists of data. *)
Module Lab_as_DT := UDT_to_DT (Lab_as_UDT).
Module Map := Make (Lab_as_DT).
Module MapFacts := WFacts_fun Map.E Map.
Definition mem A := Map.t (list (frame A)).

Definition get_frame {A} (m : mem A) (b : block) :=
    match Map.find (snd b) m with
    | Some bs => nth_error_Z bs (fst b)
    | None => None
    end.

Definition next {A} (m : mem A) (s : Label) : Z :=
    match Map.find s m with
    | Some bs => Z.of_nat (length bs)
    | None => Z0
    end.

Theorem get_frame_next {A} : forall i s (m : mem A),
      (0 <= i < next m s)%Z <-> (exists fr, get_frame m (i,s) = Some fr).
Proof.
    move => i s m; rewrite /next /get_frame.
    simpl; destruct (Map.find s m) eqn:FindS.
    { split => Hyp.
    - apply nth_error_Z_valid2.
      destruct Hyp as [H1 H2].
      split; auto.
      apply /ltP.
      apply Z2Nat.inj_lt in H2; auto.
      { rewrite Nat2Z.id in H2; auto. }
      omega.
    - destruct Hyp as [fr Hfr].
      apply nth_error_Z_valid in Hfr.
      destruct Hfr as [H1 H2].
      split; auto.
      apply Z2Nat.inj_lt; auto.
      { apply Nat2Z.is_nonneg. }
      rewrite Nat2Z.id.
      apply /ltP.
      auto.
    }
    { split => Hyp.
      - omega.
      - destruct Hyp; congruence.
    } 
Qed.

Theorem next_pos : forall {A} (m : mem A) s, (0 <= next m s)%Z.
Proof.
    intros A m s.
    rewrite /next.
    destruct (Map.find s m).
    - apply Nat2Z.is_nonneg.
    - omega.
Qed.

(* Only used in QuickChick proofs *)
Definition memory_extensionality {A} (m1 m2 : mem A)
           (H : forall b, get_frame m1 b = get_frame m2 b) : m1 = m2.
  (* I think this can actually be proved now *)
  admit.
Admitted.

Definition Z_seq z1 z2 := map Z.of_nat (iota (Z.to_nat z1) (Z.to_nat z2)).

  (*
  Definition get_blocks_at_level {A} (m : t A) (s : S) :=
    let max := next m s in
    let indices := Z_seq 1%Z (max - 1) in
    map (fun ind => (ind,s)) indices.

  Definition get_blocks {A S} (ss : list S) (m : t A S) : seq (block S) :=
    flatten (map (get_blocks_at_level m) ss).
   *)

Instance show_block : Show block :=
  {|
    show b :=
      let (z,s) := (b : block) in
      ("(" ++ show z ++ " @ " ++ show s ++ ")")%string
  |}.

Instance gen_block : GenSized block :=
  {|
    arbitrarySized := fun n => liftGen2 pair (arbitrarySized n) (arbitrarySized n)
  |}.


Definition map {A B} (f:frame A -> frame B) (m:mem A) : mem B :=
  Map.map (List.map f) m.

Lemma MapsTo_In : forall {A} m k {v : A}, Map.MapsTo k v m -> Map.In k m.
Proof. intros; exists v; auto. Qed.

Lemma map_spec : forall A B (f:frame A -> frame B) (m:mem A),
    forall b, get_frame (map f m) b = omap f (get_frame m b).
Proof.
  intros.
  rewrite /get_frame /map /omap /obind /oapp.
  destruct (Map.find b.2 m) eqn:Find.
  - remember Find as Maps. clear HeqMaps. apply Map.find_2 in Maps.
    apply Map.map_1 with (f := List.map f) in Maps.
    apply Map.find_1 in Maps.
    rewrite Maps.
    apply nth_error_Z_map.
  - destruct (Map.find b.2 (Map.map (List.map f) m)) as [? | ?] eqn:Contra; auto.
    apply Map.find_2 in Contra.
    apply MapsTo_In in Contra.
    apply Map.map_2 in Contra.
    destruct Contra as [x Hx].
    apply Map.find_1 in Hx.
    congruence.
Qed.

Definition empty A : mem A := Map.empty _.
  
Lemma get_empty : forall A b, get_frame (empty A)  b = None.
Proof. auto. Qed.

  (* Program Definition init A S {eqS : EqDec S eq} (am : alloc_mode) b f : t A S:= MEM *)
  (*   (fun b' : block S => if b' == b then Some f else None) *)
  (*   (fun s => if s == stamp _ b then fst b + 1 else 1)%Z *)
  (*   _.  *)
  (* Next Obligation. *)
  (*   simpl in *. *)
  (*   destruct (s == s0) as [EQ | NEQ]. *)
  (*   - compute in EQ. subst s0. *)
  (*     destruct (equiv_dec (i,s)) as [contra|]; trivial. *)
  (*     inv contra. *)
  (*     omega. *)
  (*   - destruct (equiv_dec (i,s)) as [E|E]; try congruence. *)
  (* Qed. *)

  (* Lemma get_init_eq : forall A S {eqS:EqDec S eq} *)
  (*                            mode (b : block S) (f : @frame A S), *)
  (*                       get_frame (init A S mode b f) b = Some f. *)
  (* Proof. *)
  (*   unfold init. simpl. *)
  (*   intros. *)
  (*   match goal with *)
  (*     | |- context [if ?b then _ else _] => *)
  (*       destruct b; congruence *)
  (*   end. *)
  (* Qed. *)

  (* Lemma get_init_neq : forall A S {eqS:EqDec S eq} *)
  (*                             mode (b b' : block S) (f : @frame A S), *)
  (*                        b' <> b -> *)
  (*                        get_frame (init A S mode b f) b' = None. *)
  (* Proof. *)
  (*   unfold init. simpl. *)
  (*   intros. *)
  (*   match goal with *)
  (*     | |- context [if ?b then _ else _] => *)
  (*       destruct b; congruence *)
  (*   end. *)
  (* Qed. *)

Definition upd_frame {A} (m:mem A) (b:block) (fr:frame A) : option (mem A) :=
  let (i,s) := b in
  match Map.find s m with
  | None => None
  | Some l =>
    match update_list_Z l i fr with
    | Some l' => Some (Map.add s l' m)
    | None => None
    end
  end.

Lemma upd_get_frame : forall A (m:mem A) (b:block) fr fr',
    get_frame m b = Some fr ->
    exists m', upd_frame m b fr' = Some m'.
Proof.
  rewrite /upd_frame /get_frame => A m b fr fr' HGet.
  destruct (Map.find b.2 m) eqn:Find.
  - apply valid_update with (x':= fr') in HGet.
    move: HGet => [l' Hl'].
    destruct b as [i s]; simpl in *.
    exists (Map.add s l' m).
    rewrite Find.
    rewrite Hl'.
    auto.
  - congruence.
Qed.

Lemma eq_refl_false : forall (A : eqType) (x : A), x == x = false -> False.
Proof. 
  move => A x H.
  pose proof (eq_refl x).
  congruence.
Qed.  

Lemma get_upd_frame : forall A (m m':mem A) (b:block) fr,
    upd_frame m b fr = Some m' ->
    forall b',
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
Proof.
  rewrite /upd_frame /get_frame => A m m' [i s] fr Hupd [i' s'] //=.
  destruct (Map.find s m) as [l|] eqn:Find;
  destruct (Map.find s' m') as [l'|] eqn:Find';
  destruct (@eq_op block_eqType (i, s) (i', s')) eqn:Eq;
  simpl in *; auto; try congruence.
  - destruct (update_list_Z l i fr) as [l'' |] eqn:Upd; try congruence.
    assert (H: @eq block (i,s) (i', s')) by (apply /eqP; auto); inv H.
    inv Hupd.
    apply Map.find_2 in Find'.
    apply MapFacts.add_mapsto_iff in Find' as [[? ?] | [? ?]]; [subst |congruence].
    eapply update_list_Z_spec; eauto.
  - destruct (update_list_Z l i fr) as [l'' |] eqn:Upd; try congruence.
    inv Hupd.
    destruct (s == s') eqn:HS.
    + assert (H : s = s') by (apply /eqP; auto); inv H.
      rewrite Find.
      apply Map.find_2 in Find'.
      apply MapFacts.add_mapsto_iff in Find' as [[? ?] | [? ?]]; [subst |congruence].
      destruct (i == i') eqn:HI.
      * assert (H' : i = i') by (apply /eqP; auto); inv H'.
        apply eq_refl_false in Eq; inv Eq.
      * assert (i <> i').
        { move => ?; subst; apply eq_refl_false in Eq; inv Eq. }
        eapply update_list_Z_spec2 in Upd; eauto.
    + apply Map.find_2 in Find'.
      apply MapFacts.add_mapsto_iff in Find' as [[? ?] | [? Find']]; subst;
      [ apply eq_refl_false in HS; inv HS |] .
      apply Map.find_1 in Find'.
      rewrite Find'.
      auto.
  - assert (H: @eq block (i,s) (i', s')) by (apply /eqP; auto); inv H.
    destruct (update_list_Z l i' fr) as [l'' |] eqn:Upd; try congruence.
    inv Hupd.
    rewrite MapFacts.add_o in Find'.
    destruct (Map.E.eq_dec s' s'); subst; try congruence.
  - destruct (update_list_Z l i fr) as [l'' |] eqn:Upd; try congruence.
    inv Hupd.
    destruct (s == s') eqn:HS.
    + assert (H : s = s') by (apply /eqP; auto); inv H.
      rewrite MapFacts.add_o in Find'.
      destruct (Map.E.eq_dec s' s'); subst; try congruence.
    + rewrite MapFacts.add_o in Find'.
      destruct (Map.E.eq_dec s s'); subst; try congruence.
      rewrite Find'.
      auto.
Qed.

(*
Definition upd_frame_rich {A} (m:mem A) (b:block) (fr:frame A)
  : option { m' : (mem A S) |
             (forall b',
                get_frame m' b' = if b0 == b' then Some fr else get_frame m b')
           /\ forall s, next m s = next m' s} :=
    match m b0 with
      | None => None
      | Some _ =>
        Some (MEM
                (fun b => if b0 == b then Some fr else m b)
                (next m) _ _)
    end.
  Next Obligation.
    split.
    - have [e|ne] := altP (b0 =P _).
      + destruct b0; inv e. eexists. reflexivity.
      + apply content_next; auto.
    - have [e|ne] := altP (b0 =P _).
      + case=> [? [?]]; inv e.
        destruct (content_next m s i) as [_ H]. apply H.
        eexists. symmetry. exact Heq_anonymous.
      + destruct (content_next m s i) as [_ H]. apply H.
  Qed.
  Next Obligation.
    destruct m. auto.
  Qed.

  Definition upd_frame {A} {S : eqType} (m:t A S) (b0:block S) (fr:@frame A S)
  : option (t A S) :=
    match upd_frame_rich m b0 fr with
      | None => None
      | Some (exist m' _) => Some m'
    end.
*)

Lemma upd_frame_defined : forall A (m m':mem A) (b:block) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.
Proof.
  rewrite /upd_frame /get_frame.
  move => A m m' [i s] fr Upd.
  destruct (Map.find s m) eqn:Find; [|congruence].
  destruct (update_list_Z l i fr) as [l'|] eqn:Upd'; [|congruence].
  inv Upd.
  apply update_list_Z_spec3 in Upd'.
  move: Upd' => [fr' Hfr'].
  exists fr'.
  simpl in *; auto.
  rewrite Find.
  auto.
Qed.

  Opaque Z.add.

  Program Definition alloc
             {A} {S : eqType} (am:alloc_mode) (m:t A S) (s:S) (fr:@frame A S)
            : (block S * t A S) :=
    ((next m s,s),
     MEM
       (fun b' => if (next m s,s) == b' then Some fr else get_frame m b')
       (fun s' => if s == s' then (1 + next m s)%Z else next m s')
       _ _).
  Next Obligation.
    have [e|ne] := (next m s, s) =P _.
    - inv e; rewrite eqxx; split.
      + intros Hrng. eexists. reflexivity.
      + intros [fr' Heq]. inv Heq. split.
        apply next_pos. omega.
    - have [e|ne'] := s =P s0.
      + inv e. split.
        * intros [Hrng1 Hrng2]. destruct (content_next m s0 i) as [H _].
          apply H. split; first assumption.
          apply Zlt_is_le_bool in Hrng2.
          rewrite -> Z.add_comm, <- Z.add_sub_assoc, Z.add_0_r in Hrng2.
          apply Zle_bool_imp_le in Hrng2. apply Zle_lt_or_eq in Hrng2.
          destruct Hrng2 as [Hrng2 | Hrng2]. assumption.
          subst. exfalso. apply ne. reflexivity.
        * intros [fr' Heq]. destruct (content_next m s0 i) as [_ H].
          unfold get_frame in Heq.
          assert (ex: (exists fr0 : frame, m (i, s0) = Some fr0))
            by (eexists; eassumption).
          destruct (H ex) as [H1 H2]. split; omega.
      + split; intro Hrng; destruct (content_next m s0 i) as [H1 H2]; auto.
  Qed.
  Next Obligation.
    have [e|ne] := s =P s0; destruct m; simpl.
    - specialize (next_pos0 s); try omega.
    - specialize (next_pos0 s0); assumption.
  Qed.

  Lemma alloc_stamp : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> stamp b = s.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_get_fresh : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Proof.
    unfold alloc; intros.
    inv H.
    destruct (content_next m s (next m s)) as [_ H].
    unfold get_frame.
    destruct (m (next m s, s)).
    - assert (ex: exists fr0 : frame, Some f = Some fr0)
        by (eexists; reflexivity).
      specialize (H ex). omega.
    - reflexivity.
  Qed.

  Lemma alloc_get_frame : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold alloc; intros.
    inv H; auto.
  Qed.

  Lemma alloc_upd : forall A (S : eqType) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Proof.
    intros A S am m b fr1 s fr2 m' H.
    unfold alloc, upd_frame in *; simpl.
    destruct (upd_frame_rich m b fr1); try congruence.
    destruct s0; inv H.
    destruct a as [_ T].
    rewrite T; auto.
  Qed.

  Lemma alloc_local :
    forall A (S : eqType) (m1 m2:t A S) s fr1 fr2,
      (forall b, stamp b = s -> get_frame m1 b = get_frame m2 b :> bool) ->
      (alloc Local m1 s fr1).1 = (alloc Local m2 s fr2).1.
  Proof.
    move=> A S [c1 n1 cn1 np1] [c2 n2 cn2 np2] s fr1 fr2.
    rewrite /get_frame /alloc /= => Pc12; congr pair.
    suff: forall i, (1 <= i < n1 s)%Z <-> (1 <= i < n2 s)%Z.
      move: (n1 s) (n2 s) (np1 s) (np2 s)=> {np1 np2} s1 s2 np1 np2 H.
      have: forall s1 s2, (1 <= s1)%Z -> (1 <= s2)%Z ->
                          (forall i, (1 <= i < s1)%Z -> (1 <= i < s2)%Z) ->
                          (s1 <= s2)%Z.
        move=> {s1 s2 np1 np2 H} s1 s2 np1 np2 H.
        have [?|p]: (s1 = 1)%Z \/ (1 < s1)%Z by omega.
          by subst s1.
        suff: (s1 - 1 < s2)%Z by move=> ?; omega.
        move: (H (s1 - 1)%Z) => ?; omega.
      move=> H'.
      move: (H' _ _ np1 np2 (fun i => (H i).1)) => H1.
      move: (H' _ _ np2 np1 (fun i => (H i).2)) => H2.
      omega.
    move=> i; rewrite -> cn1, -> cn2.
    move: (Pc12 (i, s) erefl).
    case: (c1 _) => [fr1'|]; case: (c2 _) => [fr2'|] //= _; intuition eauto.
  Qed.

  Lemma in_seq_Z:
    forall z start len,
      (0 <= start)%Z ->
      (0 <= len)%Z ->
      ((start <= z < len + start)%Z <->
       z \in (Z_seq start len)).
  Proof.
    intros z s l. intros Hle1 Hle2. split.
    - intros [H1 H2]. unfold Z_seq.
      apply/mapP. exists (Z.to_nat z); last by rewrite Z2Nat.id; omega.
      apply Z2Nat.inj_lt in H2; try omega.
      rewrite Z2Nat.inj_add in H2; try omega.
      apply Z2Nat.inj_le in H1; try omega.
      apply Z2Nat.inj_le in Hle1; try omega.
      apply Z2Nat.inj_le in Hle2; try omega.
      simpl in *. remember (Z.to_nat s) as start.
      remember (Z.to_nat l) as len.
      remember (Z.to_nat z) as z'. clear Heqlen l Heqstart s Heqz' z Hle1.
      generalize dependent start. generalize dependent z'.
      induction len as [| l IHl]; intros s start Hle1 Hle3.
      + omega.
      + simpl in *. apply le_lt_or_eq in Hle1. destruct Hle1 as [H1 | H2].
        rewrite inE; apply/orP; right. apply IHl; try omega.
        rewrite inE; apply/orP; left; apply/eqP; congruence.
    - intros HIn. unfold Z_seq in HIn.
      move/mapP in HIn. destruct HIn as [z' HIn Heq]. subst.
      assert (H: Z.to_nat s <= z' < (Z.to_nat l) + (Z.to_nat s) ->
                 (s <= (Z.of_nat z') < l + s)%Z).
      { move=> /andP [H1 H2]. split.
        apply Z2Nat.inj_le; try omega. rewrite Nat2Z.id. apply/leP. assumption.
        apply Z2Nat.inj_lt; try omega. rewrite Nat2Z.id Z2Nat.inj_add;
         try omega. apply/ltP. assumption. }
      apply H.
      apply Z2Nat.inj_le in Hle1; try omega.
      apply Z2Nat.inj_le in Hle2; try omega.
      remember (Z.to_nat s) as start.
      remember (Z.to_nat l) as len.
      clear H Heqlen l Heqstart s.
      generalize dependent start. generalize dependent z'.
      induction len as [| len IHlen].
      + by [].
      + intros z' start Hle; rewrite /= inE => /orP HIn. simpl in *.
        case: HIn => [/eqP ?|HIn]; subst.
          rewrite addnE /addn_rec; apply/andP; split; [apply/leP|apply/ltP]; omega.
        * rewrite addSn -addnS.
        assert (H': S start <= z' < len + S start ->
                    start <= z' < len + S start).
        { rewrite addnE /addn_rec.
          move=> /andP [/leP H1 /ltP H2].
          apply/andP; split; [apply/leP| apply/ltP]; try omega. }
        apply H'. apply IHlen; try omega. assumption.
  Qed.

  Lemma get_blocks_spec :
    forall A (S : eqType) (labs : seq S) (mem: t A S) b,
      (stamp b \in labs) && get_frame mem b <->
      b \in get_blocks labs mem.
  Proof.
    intros A S labs mem b.
    split.
    - case/andP => HIn.
      case Hget: get_frame => [fr|] //= _.
      unfold get_blocks; apply/flatten_mapP.
      eexists; [eassumption|].
      unfold get_blocks_at_level. apply/mapP. exists b.1;
      destruct b=> //.
      apply in_seq_Z; try omega.
      * apply Zle_minus_le_0. apply next_pos.
      * rewrite <- Z.sub_sub_distr, Z.sub_0_r. simpl.
        apply content_next. eexists. eassumption.
    - intros HIn. unfold get_blocks, get_blocks_at_level in *.
      move/flatten_mapP in HIn. destruct HIn as [l HInl HIn].
      move/mapP in HIn. destruct HIn as [z HIn Heq]. subst.
      rewrite HInl /=.
      unfold get_frame.
      suff [fr ->] : exists fr, mem (z, l) = Some fr by [].
      apply content_next. apply in_seq_Z in HIn; try omega.
      apply Zle_minus_le_0. apply next_pos.
  Qed.

End Mem.

Canonical Mem.block_eqType.

Lemma alloc_get_frame_old :
  forall T (S : eqType) mode mem (stamp : S) (f f' : @frame T S) b b' mem'
         (ALLOC : Mem.alloc mode mem stamp f' = (b', mem'))
         (FRAME : Mem.get_frame mem b = Some f),
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  have [e|//] := altP (b' =P b).
  exploit Mem.alloc_get_fresh; eauto.
  congruence.
Qed.

Lemma alloc_get_frame_new :
  forall T (S : eqType) mode mem (stamp : S) (frame : @frame T S) b mem'
         (ALLOC : Mem.alloc mode mem stamp frame = (b, mem')),
    Mem.get_frame mem' b = Some frame.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  by rewrite eqxx; simpl in *; auto.
Qed.

Lemma get_frame_upd_frame_eq :
  forall T (S : eqType)
         (m : Mem.t T S) b f m'
         (UPD : Mem.upd_frame m b f = Some m'),
    Mem.get_frame m' b = Some f.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  by rewrite eqxx.
Qed.

Lemma get_frame_upd_frame_neq :
  forall T (S : eqType)
         (m : Mem.t T S) b b' f m'
         (UPD : Mem.upd_frame m b f = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  have [?|?] := (b =P b'); simpl in *; congruence.
Qed.
