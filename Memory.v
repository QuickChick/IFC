Require Import Datatypes.
Require Import ZArith.
Require Import String.
Require Import Show.

Require Import Utils.

Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Definition zreplicate {A:Type} (n:Z) (a:A) : option (seq A) :=
  if Z_lt_dec n 0 then None
  else Some (nseq (Z.to_nat n) a).

Lemma nth_error_Z_zreplicate: forall A z (a:A) z' l,
  zreplicate z a = Some l ->
  nth_error_Z l z' = if Z_le_dec 0 z' then
                        if Z_lt_dec z' z then Some a else None
                     else None.
Proof.
  unfold zreplicate, nth_error_Z; intros.
  destruct (Z_lt_dec z 0); try congruence.
  inv H.
  destruct (z' <? 0)%Z eqn:Ez.
  - rewrite -> Z.ltb_lt in Ez.
    destruct Z_lt_dec; try omega.
    destruct Z_le_dec; auto; omega.
  - assert (~ (z' < 0 )%Z).
    rewrite <- Z.ltb_lt; try congruence.
    destruct Z_le_dec; try omega; simpl in *; inv H.
    rewrite (_ : is_left (Z_lt_dec z' z) = (Z.to_nat z' < Z.to_nat z)).
      elim: (Z.to_nat z') (Z.to_nat z) {n Ez H0 l0}=> [|n IH] [|n'] //=.
      by rewrite IH ltnS.
    assert ( (z'<z)%Z <-> (Z.to_nat z' < Z.to_nat z)%coq_nat).
      apply Z2Nat.inj_lt; try omega.
    by apply/sumboolP/ltP; intuition.
Qed.

Inductive alloc_mode := Global | Local.

(* Frames are parameterized over the type of block and the type of Label *)
(* Cannot make this a parameter because we don't want it opaque.
   Keep it outside for now, until I figure out what's better *)
(* Any better solutions than the implicit arguments welcome *)
Inductive frame {A S} := Fr (label : S) : seq A -> @frame A S.

Section FrameEqType.

Variables A S : eqType.

Definition frame_eq (fr1 fr2 : @frame A S) : bool :=
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

Canonical frame_eqType := Eval hnf in EqType (@frame A S) frame_eqMixin.

End FrameEqType.

Module Type MEM.
  (* Type of memory is parameterized by the type of stamps and the type of block *)
  Parameter t : Type -> Type -> Type.

  Parameter block : Type -> Type.
  Parameter stamp : forall {S}, block S -> S.

  Parameter block_eq : forall (S : eqType), block S -> block S -> bool.

  Parameter block_eqP : forall S, Equality.axiom (@block_eq S).

  Definition block_eqMixin (S : eqType) := EqMixin (block_eqP S).
  Canonical block_eqType (S : eqType) :=
    EqType (block S) (block_eqMixin S).

  (* For generation *)
  Parameter put_stamp : forall {S}, S -> block S -> block S.
  (* For indistinguishability - return all frames with stamps
     less than a label (called with top) *)

 (* For printing *)
  Declare Instance show_block : forall {S} {_: Show S}, Show (block S).

  (* DD -> DP : is a block some kind of "stamped pointer"? *)
  Parameter get_frame : forall {A S}, t A S -> block S -> option (@frame A S).
  Parameter upd_frame :
    forall {A} {S:eqType}, t A S -> block S -> @frame A S -> option (t A S).

  Parameter upd_get_frame : forall A (S : eqType) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Parameter get_upd_frame : forall A (S : eqType) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b',
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter upd_frame_defined : forall A (S : eqType) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.

  Parameter memory_extensionality :
    forall {A} {S : eqType} (m1 m2 : t A S),
    (forall (b : block S), get_frame m1 b = get_frame m2 b) -> m1 = m2.

  Parameter get_blocks : forall {A S} , seq S -> t A S -> seq (block S).

  Parameter get_blocks_spec:
    forall {A} {S : eqType} (labs : seq S) (mem: t A S) (b: block S),
      (stamp b \in labs) && get_frame mem b <->
      b \in get_blocks labs mem.

  Parameter empty : forall A S, t A S.
  Parameter get_empty : forall A S (b:block S), get_frame (empty A S) b = None.

  (* Create a memory with some block initialized to a frame *)
  (* Parameter init : forall A S {eqS:EqDec S eq}, *)
  (*                    alloc_mode -> *)
  (*                    block S -> *)
  (*                    @frame A S -> *)
  (*                    t A S. *)

  (* Parameter get_init_eq : forall A S {eqS:EqDec S eq} *)
  (*                                mode (b : block S) (f : @frame A S), *)
  (*                           get_frame (init A S mode b f) b = Some f. *)

  (* Parameter get_init_neq : forall A S {eqS:EqDec S eq} *)
  (*                                 mode (b b' : block S) (f : @frame A S), *)
  (*                            b' <> b -> *)
  (*                            get_frame (init A S mode b f) b' = None. *)

  Parameter alloc :
    forall {A} {S : eqType}, alloc_mode -> t A S -> S -> @frame A S -> (block S * t A S).
  Parameter alloc_stamp : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> stamp b = s.
  Parameter alloc_get_fresh : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') -> get_frame m b = None.
  Parameter alloc_get_frame : forall A (S : eqType) am (m m':t A S) s fr b,
    alloc am m s fr = (b,m') ->
    forall b', get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Parameter alloc_upd : forall A (S : eqType) am (m:t A S) b fr1 s fr2 m',
    upd_frame m b fr1 = Some m' ->
    fst (alloc am m' s fr2) = fst (alloc am m s fr2).
  Parameter alloc_local :
    forall A (S : eqType) (m1 m2:t A S) s fr1 fr2,
      (forall b, stamp b = s -> get_frame m1 b = get_frame m2 b :> bool) ->
      (alloc Local m1 s fr1).1 = (alloc Local m2 s fr2).1.

  Parameter map : forall {A B S}, (@frame A S -> @frame B S) -> t A S -> t B S.
  Parameter map_spec : forall A B S (f: @frame A S -> @frame B S) (m:t A S),
    forall b, get_frame (map f m) b = option_map f (get_frame m b).

End MEM.

(* For indist/generation purposes, our implementation has to be less generic or
   give our labels a function "allLabelsBelow". For now do the latter *)
Module Mem: MEM.
  Definition block S := (Z * S)%type.

  Definition block_eq (S : eqType) (b1 b2 : block S) := b1 == b2.

  Lemma block_eqP (S : eqType) : Equality.axiom (@block_eq S).
  Proof. move=> ??; exact/eqP. Qed.

  Definition block_eqMixin (S : eqType) := EqMixin (block_eqP S).
  Canonical block_eqType (S : eqType) :=
    EqType (block S) (block_eqMixin S).

  Definition stamp S : block S -> S := @snd _ _.
  Definition put_stamp S (s : S) (b : block S) : block S :=
    let (z,_) := b in (z,s).

  Record _t {A S} := MEM {
     content :> block S -> option (@frame A S);
     next : S -> Z;
     content_next : forall s i, (1 <= i < next s)%Z  <->
                                (exists fr, content (i,s) = Some fr);
     next_pos : forall s, (1 <= next s)%Z
     (* content_some :  *)
     (*   forall s i, (1 <= i <= (next s) -1)%Z <->  *)
     (*               (exists fr, content (i, s) = Some fr) *)
  }.

  Implicit Arguments _t [].
  Implicit Arguments MEM [A S].
  Definition t := _t.

  Definition get_frame {A S} (m:t A S) := content m.

  Definition memory_extensionality {A} {S : eqType} (m1 m2 : t A S)
             (H : forall b, get_frame m1 b = get_frame m2 b) : m1 = m2.
    admit.
  Qed.

  Definition Z_seq z1 z2 := map Z.of_nat (iota (Z.to_nat z1) (Z.to_nat z2)).

  Definition get_blocks_at_level {A S} (m : t A S) (s : S):=
    let max := next m s in
    let indices := Z_seq 1%Z (max - 1) in
    map (fun ind => (ind,s)) indices.

  Definition get_blocks {A S} (ss : list S) (m : t A S) : seq (block S) :=
    flatten (map (get_blocks_at_level m) ss).

  Instance show_block {S} {_: Show S}: Show (block S) :=
  {|
    show b :=
      let (z,s) := b in
      ("(" ++ show z ++ " @ " ++ show s ++ ")")%string
  |}.

  Program Definition map {A B S} (f:@frame A S -> @frame B S) (m:t A S) : t B S:=
    MEM
      (fun b => omap f (get_frame m b))
      (next m)
      _ _.
  Next Obligation.
    split.
    - intros Hrng. destruct (content_next m s i) as [H _]. destruct H.
      assumption. eexists. unfold get_frame. rewrite H. reflexivity.
    - intros [fr Heq]. destruct (content_next m s i) as [_ H].
      apply H. unfold get_frame in Heq. destruct (m (i, s)).
      eexists. reflexivity. discriminate.
  Qed.
  Next Obligation.
    destruct m. auto.
  Qed.

  Lemma map_spec : forall A B S (f:@frame A S -> @frame B S) (m:t A S),
    forall b, get_frame (map f m) b = omap f (get_frame m b).
  Proof.
    auto.
  Qed.

  Program Definition empty A S : t A S := MEM
    (fun b => None) (fun _ => 1%Z) _ _.
  Next Obligation.
    split. omega. intros [fr contra]. congruence.
  Qed.


  Lemma get_empty : forall A S b, get_frame (empty A S)  b = None.
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

  Program Definition upd_frame_rich {A} {S : eqType} (m:t A S) (b0:block S) (fr:@frame A S)
  : option { m' : (t A S) |
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

  Program Lemma upd_get_frame : forall A (S : eqType) (m:t A S) (b:block S) fr fr',
    get_frame m b = Some fr ->
    exists m',
      upd_frame m b fr' = Some m'.
  Proof.
    unfold upd_frame, upd_frame_rich, get_frame.
    intros.
    generalize (@erefl (option (@frame A S)) (m b)).
    generalize (upd_frame_rich_obligation_3 A S m b fr').
    generalize (upd_frame_rich_obligation_2 A S m b fr').
    generalize (upd_frame_rich_obligation_1 A S m b fr').
    simpl.
    rewrite H. intros. eauto.
  Qed.

  Lemma get_upd_frame : forall A (S : eqType) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    forall b',
      get_frame m' b' = if b == b' then Some fr else get_frame m b'.
  Proof.
    unfold upd_frame; intros.
    destruct (upd_frame_rich m b fr); try congruence.
    destruct s; inv H; intuition.
  Qed.

  Lemma upd_frame_defined : forall A (S : eqType) (m m':t A S) (b:block S) fr,
    upd_frame m b fr = Some m' ->
    exists fr', get_frame m b = Some fr'.
  Proof.
    unfold upd_frame, upd_frame_rich, get_frame.
    intros until 0.
    generalize (@erefl (option (@frame A S)) (@content A S m b)).
    generalize (upd_frame_rich_obligation_3 A S m b fr).
    generalize (upd_frame_rich_obligation_2 A S m b fr).
    generalize (upd_frame_rich_obligation_1 A S m b fr).
    simpl.
    intros.
    destruct (m b); eauto; congruence.
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
    alloc am m s fr = (b,m') -> stamp _ b = s.
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
      (forall b, stamp _ b = s -> get_frame m1 b = get_frame m2 b :> bool) ->
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
      (stamp _ b \in labs) && get_frame mem b <->
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
