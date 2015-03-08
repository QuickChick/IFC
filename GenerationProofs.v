Require Import List. Import ListNotations.
Require Import ZArith.
Require Import EquivDec.

Require Import QuickChick.
 
Require Import TestingCommon Indist Generation.
Require Import Sets GenerationProofsHelpers.

Require Import ssreflect ssrbool ssrnat eqtype.

(* The old version of the semantics for sequence is preferrable for these proofs *)
Lemma Forall2_combine : forall {A} n (gs : list (G A)) l,
  Forall2 (fun y => semGenSize y n) gs l ->
  forall x, In x (seq.zip l gs) -> semGenSize (snd x) n (fst x).
Proof. 
  move => A size gs l H.
  induction H as [| x y l l' H1 H2 Hforall ].
  + move => x HIn.
    inv HIn.
  + move => [a ga] HIn.
    simpl in *.
    case: HIn => [[]* | HIn]; subst => //=.
    by apply Hforall in HIn; simpl in HIn.
Qed.    

Lemma seqzip__Forall2 : forall {A} n (gs : list (G A)) l,
  length l == length gs ->
  (forall x, In x (seq.zip l gs) -> semGenSize (snd x) n (fst x)) ->
  Forall2 (fun y => semGenSize y n) gs l.
Proof. 
  move => A size gs.
  induction gs as [ | g gs IHg].
  + move => l Hlen HIn.
    destruct l.
    - by constructor.
    - inv Hlen.
  + move => l Hlen HIn.
    destruct l.
    - inv Hlen.
    - constructor => //.
      * apply (HIn (a,g)). by left.
      * apply IHg => //=.
        move => x HIn'.
        apply HIn.
        by right.
Qed.
    
Section Sized.

Variable size : nat.

Lemma existsHighObsLow : forall l obs,
  isHigh l obs -> isHigh H obs.
  move => l obs High.
  destruct l; destruct obs; auto.
Qed.

Lemma gen_from_length_correct: forall l,
  (Random.leq 0 (l-1))%Z ->
  semGenSize (gen_from_length l) size <--> 
  (fun z => (Z.le 0 z /\ Z.le z (l-1))).
Proof.
  move => l H' z; split => /=.
  + move => /semChooseSize H.
    apply H in H'; clear H.
    split; move : H' => /andP [/= H1 H2]; by apply Zle_bool_imp_le. 
  + move => [H1 H2].
    apply semChooseSize => //=. 
    apply/andP.                             
    split; by apply Zle_imp_le_bool.
Qed.    

Lemma gen_from_nat_length_correct: forall l,
  (Random.leq 0 (Z.of_nat l - 1))%Z ->                                      
  semGenSize (gen_from_nat_length l) size <--> 
  (fun z => (Z.le 0 z /\ Z.le z ((Z.of_nat l)-1))).
Proof.
  move => l z.
  rewrite /gen_from_nat_length.
  move/(_ (Z.of_nat l)): gen_from_length_correct; apply.
  auto.  
Qed.

Lemma gen_BinOpT_correct :
  semGenSize gen_BinOpT size <--> [set: BinOpT].
Proof.
  rewrite /gen_BinOpT /all. move => op.
  split => // _.
  apply semElementsSize.
  case : op; simpl; auto.
  - do 4 right; left; by []. (* I don't know why it doesn't get this *)
Qed.
 
Lemma gen_label_correct : semGenSize gen_label size <--> [set: Label].
Proof.
  rewrite /gen_label /all => l. split => [|?] //=.
  apply semElementsSize. case l; simpl; by tauto.
Qed.

Lemma gen_high_label_correct (obs : Label) : 
  isHigh H obs -> 
  semGenSize (gen_high_label obs) size <--> [set l : Label | isHigh l obs].
Proof.
  rewrite /gen_high_label.
  move => High l. split.
  + move => /semElementsSize H.
    destruct obs; destruct l; auto;
    simpl in H;
    try by move: H => [? | [ ? | [ ? | ?]]];
    try by move: H => [? | [ ? | ?]];
    inv H.
  + move => H.
    apply semElementsSize.
    destruct obs; destruct l; auto;
    simpl; try inv H.
    - by left.
    - by right;left.
    - by right;right;left.
    - by left.
    - by right;left.
    - by left.
    - by right; left.
Qed.
              
Section WithDataLenNonEmpty.

Variable inf : Info.
Hypothesis data_len_nonempty : data_len inf <> [].
Hypothesis code_len_correct  : Random.leq Z0 ((code_len inf) - 1)%Z.
Hypothesis data_len_positive : forall mf z, In (mf,z) (data_len inf) -> 
                                            Random.leq Z0 (z-1)%Z.
Hypothesis no_regs_positive : Random.leq Z0 ((Z.of_nat (no_regs inf)) - 1)%Z.
Hypothesis frame_sizes_correct : Random.leq C.min_frame_size C.max_frame_size.

(* PC *)

Definition pc_in_bounds (pc : Ptr_atom) :=
  let '(PAtm z l) := pc in
  (0 <= z <= (code_len inf) - 1)%Z.

Lemma gen_PC_correct:
  semGenSize (gen_PC inf) size <--> [set pc : Ptr_atom | pc_in_bounds pc].
Proof.
  rewrite /gen_PC /smart_gen /smart_gen_label /pc_in_bounds
          semBindSize (eq_bigcupl _ gen_label_correct) => pc.
  split.
  + move => [label [_ /semBindSize[z [/gen_from_length_correct H1
                                      /semReturnSize H2]]]].
    apply H1 in code_len_correct.
    by case H2.
  + move: pc => [z l] EqZ.
    exists l; split => //.
    apply semBindSize.
    rewrite /bigcup.
    exists z; split.
    * by apply gen_from_length_correct.
    * by apply semReturnSize.
Qed.


(* Pointer *)
Definition valid_pointer (ptr : Pointer) :=
  let '(Ptr mf addr) := ptr in
  (exists len, In (mf, len) (data_len inf) /\
               (0 <= addr <= len - 1)%Z).

Lemma gen_pointer_correct:
    semGenSize (gen_pointer inf) size <--> valid_pointer.
Proof.
  move => ptr. remember inf as Inf.
  destruct Inf.
  rewrite /gen_pointer /valid_pointer.
  split.
  * move => /semBindSize[[mf z] [/semElementsSize H]].
    destruct data_len.
    - by case data_len_nonempty.
    - move => /semBindSize [addr [/gen_from_length_correct CL]].
      move => /semReturnSize Ret.
      case Ret.
      exists z; split.
      case H => ?; subst; by [left | right].
      apply CL.
      by apply (data_len_positive mf z).
  * case: ptr => mf z.
    destruct data_len as [|x xs] eqn:DL.
    - by case data_len_nonempty.
    - move => [len [HIn EqZ]].
      apply semBindSize.
      exists (mf, len); split.
      + apply semElementsSize.
        subst; simpl in HIn.
        case HIn => ?; by [left | right].
      + apply semBindSize.
        exists z; split.
        * apply gen_from_length_correct => //=.
          move: EqZ => [HL HH].
          assert (0 <= len - 1)%Z by (eapply Z.le_trans; eassumption).
          by apply Zle_imp_le_bool.                              
        * by apply semReturnSize.
Qed.

(* Int *) 
Definition int_spec (z : Z) : Prop :=
  (- Z.of_nat size <= z <= Z.max (Z.of_nat size) (code_len inf - 1))%Z.

Lemma gen_int_correct :
  semGenSize (gen_int inf) size <--> int_spec.
move => z.
split.
+ move => /semFrequencySize /= [[freq g] [H1 H2]].
  case: H1 => [[] * | [[] * | [[] * | //]]]; subst.
  - move: H2 => /arbInt_correct [? ?].
    split; [ omega | ].
    eapply Z.le_trans; eauto.
    by apply Z.le_max_l.
  - move: H2 => /semReturnSize /= H; case H.
    split; [ omega | ].
    eapply (Z.le_trans _ (Z.of_nat size) _); [ omega | ].
    by apply Z.le_max_l.
  - move: H2 => /gen_from_length_correct H.
    apply H in code_len_correct.
    split; [ omega | ];
    eapply (Z.le_trans _ (code_len inf - 1) _); [ omega | ].
    by apply Z.le_max_r.
+ move => [ZMin ZMax].
  apply semFrequencySize => /=.
  case (Z_lt_le_dec z 0) => ZLt0.
  - eexists; split.
    * by left.
    * apply arbInt_correct.
      split; omega.
  - case (Z.max_spec (Z.of_nat size) (code_len inf - 1)).
    * move => [_ H]; subst; simpl in *.
      rewrite H in ZMax.
      eexists; split.
      + by [right; right; left].
      + apply gen_from_length_correct => //=; omega.
    * move => [_ H]; subst; simpl in *.
      rewrite H in ZMax.
      eexists; split.
      + by left.
      + apply arbInt_correct; omega.
Qed.
    
(* Value *)

Definition val_spec (v : Value) : Prop :=
  match v with
    | Vint n => int_spec n
    | Vptr ptr => valid_pointer ptr
    | Vlab l => True
  end.

(* Largely similar proofs now, should probably automate part of it *)
Lemma gen_value_correct:
    semGenSize (gen_value inf) size <--> val_spec.
Proof. 
  rewrite /gen_value /val_spec.
  remember inf as Inf.
  clear data_len_nonempty.
  clear code_len_correct.
  clear data_len_positive.
  clear no_regs_positive.
  case : Inf HeqInf => def clen dlen reg HeqInf.
  case; rewrite HeqInf.
  + (* VInt *)
    Opaque gen_int.
    move => z. 
    split => //.
    - move => /semFrequencySize /=.
      move => [[freq g] [H1 /= H2]].
      case: H1 => [[_ Heq] | [[_ Heq] | [[_ Heq] | //]]]; rewrite <- Heq in H2;
      apply semLiftGenSize in H2;
      move: H2 => [? [H1 H2]];
      case: H2 => // <-.
      by apply gen_int_correct in H1.
    - move => ZSpec.
      apply semFrequencySize => /=.
      eexists; split.                                  
      * by left.
      * simpl. apply semLiftGenSize.
        exists z; split => //.
        by apply gen_int_correct.                              
  + (* Vptr *)
    Opaque gen_pointer valid_pointer.
    case => mf addr.
    split.
    - move => /semFrequencySize /=.
      move => [[freq g] [H1 /= H2]].
      case: H1 => [[_ Heq] | [[_ Heq] | [[_ Heq] | //]]]; rewrite <- Heq in H2;
      apply semLiftGenSize in H2;
      move: H2 => [? [H1 H2]];
      case: H2 => // <-.
      by apply gen_pointer_correct in H1.
    - move => ZSpec.
      apply semFrequencySize => /=.
      eexists; split.                                  
      * by right; left.
      * simpl. apply semLiftGenSize.
        exists (Ptr mf addr); split => //.
        by apply gen_pointer_correct.                              
   + (* Vlab *)
     move => L. split => // _.
     apply semFrequencySize => /=.
     eexists; split.     
     * by [right; right; left].
     * simpl. apply semLiftGenSize.
       eexists; split => //.
       by apply gen_label_correct.
Qed.

(* Atom *)

Definition atom_spec atm  :=
  let '(Atm val lab) := atm in
  val_spec val.

Lemma gen_atom_correct:
    semGenSize (gen_atom inf) size <--> atom_spec.
Proof.
  move => [val lab]. rewrite /gen_atom. 
  split.
  + move => /semLiftGen2Size /=.
    move => [[val' lab'] [H1 H2]].
    inversion H2; subst; clear H2.
    case: H1 => /= [H1 H2].
    by apply gen_value_correct.
  + move => H /=.
    apply semLiftGen2Size.
    eexists; split => /= ; try split => /=.
    - eapply gen_value_correct.
      rewrite /atom_spec in H.
      by instantiate (1 := (val, lab)).
    - by apply gen_label_correct.      
    - by [].
Qed.       

(* regSet  *)

Definition regs_spec regs :=
  (length regs = no_regs inf) /\
  (forall reg, In reg regs -> atom_spec reg).

Lemma gen_registers_correct:
  semGenSize (gen_registers inf) size <--> regs_spec.
Proof.
  move => regs.
  rewrite /gen_registers. split.
  + move /semVectorOfSize => [H1 H2].
    split => //. move => reg HIn. by apply/gen_atom_correct; apply H2.
  + move => [Hlen Hregs]. apply/semVectorOfSize. split => // x HIn.
    apply/gen_atom_correct. by apply Hregs.
Qed.

(* stack_loc *)

Definition valid_reg_ptr ptr_r := 
  (Z0 <= ptr_r <= (Z.of_nat (no_regs inf) - 1))%Z.

Definition stack_loc_spec (t : StackFrame) : Prop :=
  let '(SF ptr_a regs ptr_r lab) := t in
  regs_spec regs /\
  valid_reg_ptr ptr_r /\
  let 'PAtm addr lab' := ptr_a in
  (0 <= addr <= ((code_len inf) - 1))%Z.

Lemma gen_stack_loc_correct :
    (semGenSize (smart_gen_stack_loc inf) size <--> stack_loc_spec).
Proof.
  rewrite /smart_gen_stack_loc /smart_gen semBindSize.
  split.
  + move => [regs' [/gen_registers_correct Hregs]].
    move /semBindSize => [[pca pcl] []] Hpc.
    move /semBindSize => [ptr_r []] Hptr_r.
    move /semBindSize => [lab []] Hlab.
    move => /semReturnSize H.
    inv H.
    rewrite /stack_loc_spec.
    do 2 split => //. 
    - apply gen_from_nat_length_correct in Hptr_r.
      * by case Hptr_r.
      * by apply no_regs_positive.
    - by apply gen_PC_correct in Hpc.

  + case: a => [[ret_pc_val ret_pc_lab] regs ptr_r lab] [[Hlen Hregs] [Hptr Hpc_val]]. 
    exists regs; split => //=.
    - by apply gen_registers_correct.                            
    apply semBindSize.
    exists (PAtm ret_pc_val ret_pc_lab); split.
    - by apply gen_PC_correct.
    apply semBindSize.
    exists ptr_r; split.
    - by apply gen_from_nat_length_correct.
    apply semBindSize.
    exists lab; split. 
    - by apply gen_label_correct.
    by apply semReturnSize.
Qed.

(* Stack *)

Definition stack_spec (s: Stack) : Prop :=
  s = ST nil \/
  exists loc, s = ST (loc :: nil) /\ stack_loc_spec loc.

Lemma gen_stack_correct: 
    semGenSize (smart_gen_stack inf) size <--> stack_spec.
Proof.
  Opaque smart_gen_stack_loc.
  rewrite /smart_gen_stack /stack_spec. move => st.
  split.
  + move/semFrequencySize => /= [[freq g] [H1 /= H2]].
    case: H1 => [[] * | [[] * | //]]; subst.
    - apply semReturnSize in H2. by left; case H2.
    - move: H2 => /semBindSize [sf [/gen_stack_loc_correct H1 /semReturnSize H2]].
      right; exists sf; split => /= //.
  + move => [StNil | [sf [H1 H2]]]; subst; apply semFrequencySize => /=.
    - eexists; split => /= //.
      * by left.
      * by apply semReturnSize.
    - eexists; split => /= //.
      * by right; left.
      * apply semBindSize. 
        exists sf; split => /= //.
        + by apply gen_stack_loc_correct.
        + by apply semReturnSize.
Qed.

(* frame *)

Definition mem_single_upd_spec mem mf (mem' : memory) :=
  match Mem.get_frame mem mf with
    | Some (Fr stamp lab data) =>
      exists fr, Mem.upd_frame mem mf fr = Some mem' /\
                 let 'Fr stamp' lab' data' := fr in
                 lab' = lab /\ stamp' = stamp /\
                 length data' = length data /\
                 forall atm, In atm data' -> atom_spec atm
    | None => mem' = mem
  end.

Lemma populate_frame_correct :
  forall mem mf,
    semGenSize (populate_frame inf mem mf) size <--> (mem_single_upd_spec mem mf).
Proof.
  move=> mem mf mem'.  rewrite /populate_frame /mem_single_upd_spec.
  remember (Mem.get_frame mem mf) as opt.
  case: opt Heqopt => [fr | ] Heqopt.
  case: fr Heqopt => stamp lab data Heq.
  - symmetry in Heq. move/Mem.upd_get_frame : (Heq) => Hupd.
    split.
    + move /semBindSize => [atmlst [/semVectorOfSize [Hl Hvec] HMatch]].
      move/(_ (Fr stamp lab atmlst)): Hupd => [fr Hfr].
      rewrite Hfr /= in HMatch;
      apply semReturnSize in HMatch.
      inversion HMatch; subst; clear HMatch.
      exists (Fr stamp lab atmlst); repeat split => /= //.
      move => atm HIn. apply gen_atom_correct. by apply Hvec.
    + move => [fr [Hget H]].
      case: fr Hupd Hget H =>
        stamp' lab' data' Hupd Hget [Heq1 [Heq2 [Heq3 H]]]; subst.
      apply semBindSize.
      exists data'. split.
      apply semVectorOfSize. split => // x HIn. by apply/gen_atom_correct; eauto.
      rewrite Hget. by apply semReturnSize.
  - split. 
    + move => /semReturnSize H. by case H.
    + by move => H; subst; apply semReturnSize.
Qed.

(* Memory *)

Lemma zreplicate_spec :
  forall {A} (v : A) (z : Z),
    (0 <= z)%Z ->
    exists (l : list A),
      (forall x, In x l -> x = v) /\
      length l = Z.to_nat z /\
      zreplicate z v = Some l.
Proof.
  move => A v z Hle. exists (replicate (Z.to_nat z) v).
  repeat split.
  - move=> x HIn. apply Z2Nat.inj_le in Hle; try omega.
    induction (Z.to_nat z) as [| n IHn].
    + contradiction.
    + destruct HIn as [Heq | HIn]; try (symmetry; assumption).
      apply IHn; auto; simpl; omega.
  - apply Z2Nat.inj_le in Hle; try omega.
    induction (Z.to_nat z) as [| n IHn].
    + reflexivity.
    + simpl. rewrite IHn; auto; simpl; omega.
  - rewrite /zreplicate. destruct (Z_lt_dec z 0); try reflexivity.
    omega.
Qed.

Lemma zreplicate_eq :
  forall {A} (l: list A) v z,
    (0 <= z)%Z ->
    (forall x, In x l ->  x = v) ->
    length l = Z.to_nat z ->
    zreplicate z v = Some l.
Proof.
  move => A l v x Hle HIn Heq.
  rewrite /zreplicate. destruct ( Z_lt_dec x 0 ) as [H | H].
  - omega.
  - apply Z2Nat.inj_le in Hle; try omega.
    clear H Hle. generalize dependent l. induction (Z.to_nat x) as [| n IHn].
    + simpl. intros l. destruct l; try discriminate. reflexivity.
    + simpl. intros l HIn Hlen. apply f_equal. destruct l; try discriminate.
      rewrite (HIn a (in_eq a l)). apply f_equal.
      inversion Hlen as [Hlen'].
      assert (Hsome: Some (replicate n v) = Some l).
      { apply IHn; auto. intros x' HIn'. apply HIn. apply in_cons.
        assumption. } rewrite Hlen'.
      inversion Hsome. reflexivity.
Qed.

Definition init_mem_spec (size : nat) (m : memory)
           (blocks : list (mframe * Z)) (m': memory)
  (blocks': list (mframe * Z)) :=
  exists (lst : list (Label * (list Atom))),
    length lst = size /\
    (forall l data,
        In (l, data) lst ->
        (C.min_frame_size <= Z.of_nat (length data) <= C.max_frame_size)%Z /\
        (forall v, In v data ->  v = (Vint 0 @ bot))) /\
    (m', blocks') =
    fold_left
      (fun (ml : memory * (list (mframe * Z))) (elem : Label * (list Atom))  =>
         let '(l, data) := elem in
         let '(m_i, bs) := ml in
         let (b, m) := Mem.alloc Local m_i bot (Fr bot l data) in
         (m, (b, Z.of_nat (length data)) :: bs)
      ) lst (m, blocks).

Definition mem_constraints (m : memory) :=
  forall b l st data,
    Mem.get_frame m b = Some (Fr st l data) ->
    (C.min_frame_size <= Z.of_nat (length data) <= C.max_frame_size)%Z /\
    st = bot /\ Mem.stamp b = bot.

(* (* CH: now unused *) *)
(* Lemma all_bellow_top : forall l, *)
(*   In l (allThingsBelow top). *)
(* Proof. rewrite /allThingsBelow. case; simpl; tauto. Qed. *)

Lemma gen_init_mem_helper_correct:
  forall (n: nat) (m : memory) (blocks : list (mframe * Z)),
    (mem_constraints m) ->
    semGenSize (gen_init_mem_helper n (m, blocks)) size <-->
    (fun p => init_mem_spec n m blocks (fst p) (snd p)).
Proof. 
  move => n m blocks Hspec [m' lst']. rewrite /init_mem_spec. split. 
  { move => Hgen. generalize dependent m. generalize dependent blocks.
      induction n as [| n IHn]; intros blocks mem Hspec Hgen. 
      - exists []. repeat split => /= //.
        rewrite /gen_init_mem_helper in Hgen. by apply semReturnSize in Hgen.
      - rewrite /gen_init_mem_helper in Hgen.
        fold gen_init_mem_helper in Hgen.
        apply semBindSize in Hgen.
        move : Hgen => [len [Hchoose /semBindSize [lab [Hlab Hgen]]]].

        move: Hchoose => /semChooseSize H. 
        apply H in frame_sizes_correct; clear H. 
        move: frame_sizes_correct => /andP [/= /Zle_bool_imp_le Hle1 /Zle_bool_imp_le Hle2].
        rewrite /C.min_frame_size /C.max_frame_size in Hle1 Hle2 *.
        unfold alloc in Hgen.
        destruct (zreplicate_spec (Vint 0 @ ⊥) len) as [data [HIn [Heq HSome]]].
        simpl in *; omega. rewrite HSome in Hgen.
        remember (Mem.alloc Local mem ⊥ (Fr ⊥ lab data)) as alloc.
        destruct alloc as [fr mem'].
        destruct (IHn ((fr, Z.of_nat (length data)) :: blocks) mem')
          as [lst [Hlen [Hforall Hfold]]] => //; clear IHn.
        + rewrite /init_mem_spec in Hspec *.
          symmetry in Heqalloc. move : (Heqalloc) => Halloc.
          move => fr' lab' st' data' Hget.
          apply Mem.alloc_get_frame with (b' := fr') in Halloc.
          destruct (equiv_dec fr fr').
          * inv e. rewrite Halloc in Hget. inv Hget.
            rewrite /C.min_frame_size /C.max_frame_size Heq.
            repeat split => //=; try (simpl in *; rewrite Z2Nat.id; omega).
            by eapply Mem.alloc_stamp; apply Heqalloc.
          * eapply Hspec. rewrite -Halloc. eassumption.
        + rewrite Heq. simpl in *; rewrite Z2Nat.id. by []. omega.
        + exists ((lab, data) :: lst). split. by subst.
          split => //=. 
          * move => l data' [[eq1 eq2] | H]; subst. 
            split => //. rewrite Heq //. rewrite Z2Nat.id. split => //. 
            eapply Z.le_trans; [| apply Hle1] => //.
            edestruct Hforall as [Hrng HIn']. apply H. 
            split; auto. simpl in Hfold. rewrite Hfold.
            by rewrite -Heqalloc. }
  { move => [lst [Hlen [HIn Hfold]]]. generalize dependent lst.
    generalize dependent m. generalize dependent blocks.
    induction n as [| n IHn]; intros blocks m Hspec lst Hlen HIn Hfold.
    - destruct lst; simpl in *.
      by apply semReturnSize. 
      congruence.
    - rewrite /gen_init_mem_helper. fold gen_init_mem_helper. apply semBindSize.
      destruct lst as [|[lab data] lst]. simpl in Hlen; congruence.
      destruct (HIn lab data) as [[Hle1 Hle2] HInx]; try by apply in_eq.
      exists (Z.of_nat (length data)). split.
      + apply semChooseSize.
        by apply frame_sizes_correct.
        apply/andP. 
        split; by apply Zle_imp_le_bool.
      + apply semBindSize.
        exists lab. split; try by apply gen_label_correct.
        rewrite /alloc.
        rewrite (zreplicate_eq data); auto; try omega; try by rewrite Nat2Z.id.
        remember (Mem.alloc Local m L (Fr L lab data)) as frm.
        destruct frm as [fr1 m1]. rewrite -Heqfrm.
        apply IHn with (lst := lst).
        * rewrite /init_mem_spec in Hspec *.
          move => block lab' st' data' Hget.
          symmetry in Heqfrm. move: (Heqfrm)=> Halloc.
          apply Mem.alloc_get_frame with (b' := block) in Halloc.
          destruct (equiv_dec fr1 block).
          - inv e.  rewrite Hget in Halloc. inv Halloc.
            split => //. split => //.
            eapply Mem.alloc_stamp.
            apply Heqfrm.
          - rewrite Halloc in Hget. rewrite /mem_constraints in Hspec.
              eapply Hspec; by eauto.
       * by inversion Hlen.
       * move => lab' data' HIn'.
         apply in_cons with (a := (lab, data)) in HIn'. by apply HIn in HIn'.
       * simpl in Hfold. by rewrite -Heqfrm in Hfold. }
Qed.

Lemma gen_init_mem_correct:
  forall (top : Label),
    semGenSize gen_init_mem size <-->
    (fun ml =>
       (exists n,
          C.min_no_frames <= n <= C.max_no_frames /\
          init_mem_spec n (Mem.empty Atom Label) [] (fst ml) (snd ml))).
  Proof.
    move => top init_mem. split.
    { unfold gen_init_mem.
      move => /semBindSize [len [Hchoose Hgen]].
      exists len. apply semChooseSize in Hchoose.
      move: Hchoose => /andP [/= Hle1 Hle2]. simpl in *.
      edestruct (gen_init_mem_helper_correct len (Mem.empty Atom Label))
        as [Hl _].
      - move => b l st data Hget.
        by rewrite Mem.get_empty in Hget.
      - destruct (Hl Hgen) as [lst H].
        split => //. apply/andP. split => //. 
        by eauto. 
        assumption.
    }
    { move => [len [/andP [Hle1 Hle2] Hspec]].
      edestruct (gen_init_mem_helper_correct len (Mem.empty Atom Label))
        as [_ Hr].
      - rewrite /init_mem_spec /=. move => b l st data Hget.
        by rewrite Mem.get_empty in Hget.
      - rewrite /gen_init_mem.
        apply semBindSize.
        exists len. split.
        + apply semChooseSize. split => //.
          apply/andP. by split.
          by auto. 
    }
Qed.

Definition init_mem_single_upd_spec (mem : Mem.t Atom Label)
           (mf : Mem.block Label) (mem' : memory) :=
  match Mem.get_frame mem mf with
    | Some (Fr stamp lab data) =>
      exists fr : Memory.frame,
        Mem.upd_frame mem mf fr = Some mem' /\
        (let 'Fr stamp' lab' data' := fr in
         lab' = lab /\
         stamp' = stamp /\
         length data' = length data /\
         (forall atm : Atom, In atm data' -> atom_spec atm))
    | None => mem' = mem
  end.

Definition populated_memory_spec (m : memory) (m': memory) :=
  let blocks := map fst (data_len inf) in
  seq.foldr (fun block (p : memory -> Prop) m_prev =>
               exists m, (mem_single_upd_spec m_prev block m) /\ p m)
            (eq m') blocks m /\
  (forall b st lab d,
     Mem.get_frame m' b = Some (Fr st lab d) ->
     st = bot /\
     Mem.stamp b = bot /\
     (C.min_frame_size <= Z.of_nat (length d) <= C.max_frame_size)%Z).

(* Lemma semFoldGen_right :
  forall {A B : Type} (f : A -> B -> G A) (bs : list B) (a0 : A) (s : nat),
    semGenSize (foldGen f bs a0) s <-->
    [ set an |
      foldr (fun b p => [set a_prev | exists a, a \in (semGenSize (f a_prev b) s :&: p)]) 
            [set an] bs a0].
Pr *)

Lemma populate_memory_correct:
  forall (m : memory),
    mem_constraints m ->
    semGenSize (populate_memory inf m) size <-->
    (populated_memory_spec m ).
Proof.
  move => m Hcontent m'.
  split.
  { unfold populate_memory.
    move => /semFoldGen_right Hgen. rewrite /populated_memory_spec.
    generalize dependent m.
    set lst := ((map fst (data_len inf))).
    induction lst as [| b bs IHbs]; move=> m Hinit Hfold.
    rewrite /mem_constraints in Hinit.
    - simpl in *; subst. 
      inversion Hfold; subst; clear Hfold.
      split => // b st l d /Hinit [? [? ?]];
      by repeat split => //.
   - simpl in *. move: Hfold => [m'' [Hpop Hfold]].
     have Hcnstr: mem_constraints m''.
     { rewrite /populate_frame in Hpop.
       remember (Mem.get_frame m b) as get.
       destruct get as [[st l d]|]. 
       * symmetry in Heqget.
         apply semBindSize in Hpop.
         case : Hpop => [d' [/semVectorOfSize [Hlen Hforall] Hupd]].
         destruct (Mem.upd_get_frame _ _ _ _ _ _ (Fr st l d') Heqget)
           as [fr Hupd'].
         rewrite Hupd' in Hupd. 
         apply semReturnSize in Hupd. 
         inv Hupd. rewrite /mem_constraints.
         destruct (Hinit _ _ _ _ Heqget) as [? [? ?]].
         subst. move => b' l' st' d'' Hget.
         move: (Mem.get_upd_frame _ _ _ m m'' _ _ Hupd' b') => Hget'.
         case: (equiv_dec b b') Hget' => e Hget'.  inv e.
         - rewrite Hget in Hget'. inv Hget'. split => //.
           split; [rewrite Hlen | repeat split => //]; omega.
         - rewrite Hget in Hget'. symmetry in Hget'.
           destruct (Hinit _ _ _ _ Hget') as [? [? ?]].
           by repeat split => //.
       * apply semReturnSize in Hpop; by inv Hpop.
     }
     destruct (IHbs m'' Hcnstr Hfold) as [Hfold' Hcnstr']. split => //.
     exists m''. split=> //.
     by apply populate_frame_correct. }
  { rewrite /populated_memory_spec /populate_memory. move => [Hfold Hconstr].
    apply semFoldGen_right. generalize dependent m.
    set lst := ((map fst (data_len inf))).
    induction lst as [| b bs IHbs]; move=> m Hinit Hfold.
    + by simpl in *.
    + simpl in *. move : Hfold => [m'' [Hupd Hfold]]. eexists. split => //.
      * apply populate_frame_correct. eassumption.
      * apply IHbs => //. rewrite /mem_single_upd_spec in Hupd.
       remember (Mem.get_frame m b) as get.
       destruct get as [[st l d]|]; try by inv Hupd.
       symmetry in Heqget.
       move : Hupd => [[st' l' d'] [Hupd' [eq1 [eq2 [Hlen Hforall]]]]]; subst.
       destruct (Mem.upd_get_frame _ _ _ _ _ _ (Fr st l d') Heqget)
         as [fr Hupd''].
       rewrite Hupd'' in Hupd'. inv Hupd'. rewrite /mem_constraints.
       destruct (Hinit _ _ _ _ Heqget) as [? [? ?]].
       subst. move => b' l' st' d'' Hget.
       move: (Mem.get_upd_frame _ _ _ m m'' _ _ Hupd'' b') => Hget'.
       case: (equiv_dec b b') Hget' => e Hget'.  inv e.
       - rewrite Hget in Hget'. inv Hget'. split => //.
         split; [rewrite Hlen | repeat split => //]; omega.
       - rewrite Hget in Hget'. symmetry in Hget'.
         destruct (Hinit _ _ _ _ Hget') as [? [? ?]].
         repeat split => //. }
Qed.

(* Instruction *)

(*
Definition Instruction_spec (st : State) (instr : @Instr Label) :=
  let '(St im m stk regs pc ) := st in
  let '(dptr, cptr, num, lab) :=
      groupRegisters st regs [] [] [] [] Z0 in
  match instr with
    | Put _ z => (0 <= z <= (Zlength regs -1))%Z
    | Move z1 z2 => (0 <= z1 <= (Zlength regs -1))%Z /\ (0 <= z2 <= (Zlength regs-1))%Z

    | MLab z1 z2 | Load z1 z2 | Store z1 z2 | MSize z1 z2 | PGetOff z1 z2 | PSetOff z1 z2 
    | Write z1 z2 =>
      dptr <> [] /\ In z1 dptr /\  (0 <= z2 <= (Zlength regs-1))%Z
                                                  
    | Nop => True | Halt => False
    | PcLab z | PutLab _ z 
    | Lab z1 z2 =>
      (0 <= z1 <= (Zlength regs-1))%Z /\ (0 <= z2 <= (Zlength regs-1))%Z
 
    | FlowsTo z1 z2 z3 | LJoin z1 z2 z3 =>
      lab <> [] /\ In z1 lab /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BCall z1 z2 z3 =>
      cptr <> [] /\ lab <> [] /\
      In z1 cptr /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | BRet => (containsRet stk = true)
    | Alloc z1 z2 z3 =>
      num <> [] /\ lab <> [] /\
      In z1 num /\ In z2 lab /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Jump z => cptr <> [] /\ In z cptr
    | BNZ z1 z2 => num <> [] /\ (-1 <= z1 <= 2)%Z /\ In z2 num
    | PSetOff z1 z2 z3 =>
      dptr <> [] /\ num <> [] /\
      In z1 dptr /\ In z2 num /\  (0 <= z3 <= (Zlength regs-1))%Z
    | Output z1 =>
      num <> [] /\ In z1 num
    | BinOp _ z1 z2 z3 =>
      num <> [] /\ In z1 num /\ In z2 num /\ (0 <= z3 <= (Zlength regs-1))%Z
  end.

Ltac discr_gen_eq :=
  match goal with
    | H : (_, liftGen ?f ?gen) = (?n, ?g),
      Hg : ?g _ |- _ =>
        move : H => [Heq1 Heq2]; subst;
        rewrite liftGen_def in Hg; move: Hg => [a [_ H]]; discriminate
    | H : (_, returnGen ?a) = (?n, ?g),
      Hg : ?g _ |- _ =>
        move : H => [Heq1 Heq2]; subst; discriminate
    | H : (_, liftGen2 ?f ?gen1 ?gen2) = (?n, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen2_def in Hg;
      move: Hg => [a [_ [a' [_ H]]]]; subst; discriminate
    | H : (_, liftGen3 ?f ?gen1 ?gen2 ?gen3) = (?n, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen3_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ H]]]]]]; subst; discriminate
    | H : (_, liftGen4 _ _ _ _ _) = (_, ?g),
      Hg : ?g _ |- _ =>
      move : H => [Heq1 Heq2]; subst;
      rewrite liftGen4_def in Hg;
      move: Hg => [a [_ [a' [_ [a'' [ _ [a''' [ _ H]]]]]]]]; subst; discriminate

  end.

Ltac discr_or_first :=
  match goal with
    | HIn : ((_, _) = (_ , _) \/ _) |- _ =>  case: HIn => [Heq | HIn]; [discr_gen_eq | ]
    | HIn : In (_, _) _ |- _ => case: HIn => [Heq | HIn]; [discr_gen_eq | ]
  end.


Ltac unfold_gen :=
  match goal with
    | Hg : returnGen _ _ |- _ =>
      rewrite returnGen_def in Hg; subst
    | Hg : liftGen _ _ _ |- _ =>
      rewrite liftGen_def in Hg; move: Hg => [b [H1 [Heq]]]; subst
    | Hg : liftGen2 _ _ _ _ |- _ =>
      rewrite liftGen2_def in Hg;
        move: Hg => [b [H1 [b' [H2 [Heq1 Heq2]]]]]; subst
    | Hg : liftGen3 _ _ _ _ _ |- _ =>
      rewrite liftGen3_def in Hg;
        move: Hg => [b [H1 [b' [H2 [b'' [H3 [Heq1 Heq2 Heq3]]]]]]]; subst
    | Hg : liftGen4 _ _ _ _ _ _ |- _ =>
      rewrite liftGen4_def in Hg;
       move: Hg=>[b [H1 [b' [H2 [b'' [ H3 [b''' [H4 [Heq1 Heq2 Heq3 Heq4]]]]]]]]]; subst
  end.

Ltac try_solve :=
      match goal with
        | |- _ /\ _ => split => //=; by try_solve
        | Hand : _ /\ _ |- _ => destruct Hand; by try_solve
        | Hor : _ \/ _ |- _ => destruct Hor; by try_solve
        | |- ~ _ => move => contra; subst; by try_solve
        | Hchoose : choose _ _ |- _ =>
          rewrite choose_def /= in Hchoose; by try_solve
        | Helem : elements _ _ _ |- _ =>
          move/elements_equiv : Helem => [Helem //= | [Helem1 Helem2] //=]; subst;
          by try_solve

        | HIn: In _ [] |- _ => by []
        | Hnonempty : ~ (onNonEmpty [] _ = 0) |- _ =>
           by rewrite /onNonEmpty in Hnonempty
        | Hnonempty : ~ (_ * (onNonEmpty [] _))%coq_nat = 0 |- _ =>
            by rewrite [X in (_ * X)%coq_nat]/onNonEmpty -mult_n_O in Hnonempty
        | Hif: ~ ((if ?b then _ else _ ) = _) |- ?b = true =>
            by case: b Hif
        | |- (_ <= _)%Z => by apply/Zle_bool_imp_le
        | |- _ => by []
      end. 



Ltac find_instr instr lst k :=
  match lst with
    | nil => k 0 (pure Nop)
    | (?n, liftGen4 ?c ?a1 ?a2 ?a3 ?a4) :: ?lst' => (* match with liftGen4 *)
      match instr with
        | c _ _ _ _ => k n (liftGen4 c a1 a2 a3 a4)
        | _ => find_instr instr lst' k
      end
    | (?n, liftGen3 ?c ?a1 ?a2 ?a3) :: ?lst' => (* match with liftGen3 *)
      match instr with
        | c _ _ _ => k n (liftGen3 c a1 a2 a3)
        | _ => find_instr instr lst' k
      end
    | (?n, liftGen2 ?c ?a1 ?a2) :: ?lst' => (* match with liftGen2 *)
      match instr with
        | c _ _  => k n (liftGen2 c a1 a2)
        | _ => find_instr instr lst' k
      end
    | (?n, liftGen ?c ?a1) :: ?lst' => (* match with liftGen *)
      match instr with
        | c _  => k n (liftGen c a1)
        | _ => find_instr instr lst' k
      end
    | (?n, ?f ?c) :: ?lst' => (* match with pure/returnGen *)
      match instr with
        | c  => k n (f c)
        | _ => find_instr instr lst' k
      end
  end.


Ltac instantiate_exists :=
  match goal with
    | |- exists n g, In (n, g) ?lst /\ _ ?cnstr /\ _ =>
      find_instr cnstr lst ltac:(fun n g => pose cnstr; exists n; exists g);
      split; [repeat ((try by apply in_eq); apply in_cons) | split => //]
  end.

Ltac try_solve2 :=
  match goal with
    | Hand : _ /\ _ |- _ => destruct Hand; by try_solve2
    | |- _ = _ => reflexivity
    | |- _ /\ _ => split; [| by try_solve2]; by try_solve2
    | |- liftGen4 _ _ _ _ _ _ => rewrite liftGen4_def; by try_solve2
    | |- liftGen3 _ _ _ _ _ => rewrite liftGen3_def; by try_solve2
    | |- liftGen2 _ _ _ _ => rewrite liftGen2_def; by try_solve2
    | |- liftGen _ _ _ => rewrite liftGen_def; by try_solve2
    | |- elements _ _ _ => apply/elements_equiv; left; by try_solve2
    | |- choose _ _ => rewrite choose_def => /=; by try_solve2
    | |- is_true (_ <=? _)%Z => by apply/Zle_imp_le_bool
    | |- gen_from_length _ _ => rewrite /gen_from_length; try try_solve2
    | |- ~ onNonEmpty ?l _ = 0 => by destruct l
    | |- exists _, _ => eexists; by try_solve2
    | |- ~ (( _ * onNonEmpty ?c _)%coq_nat * onNonEmpty ?l _)%coq_nat = 0 =>
        by destruct c; destruct l
    | |- gen_BinOpT _ => by apply gen_BinOpT_correct
    | |- ~ (if ?b then _ else _) = 0 => by destruct b
    | _ => by []
  end. 
 


 
Lemma gen_ainstrSSNI_correct :
  forall (st : State), (ainstrSSNI st) <--> (Instruction_spec st).
Proof.
  move=> st instr. rewrite /ainstrSSNI /Instruction_spec.
  case: st => im m stk regs pc.
  set st := {|
             st_imem := im;
             st_mem := m;
             st_stack := stk;
             st_regs := regs;
             st_pc := pc |}.
  case: (groupRegisters st regs [] [] [] [] Z0)=> [[[dptr cptr] num] lab].
  split.
  - case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 |
                    l r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 |
                    r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2];
    move /frequency_equiv =>  [[n [g [HIn [Hg Hn]]]] | [[H | H] H' //=]];
    rewrite /gen_from_length /pure in HIn; repeat discr_or_first;
    (case: HIn => [[Heq1 Heq2] | HIn]; subst;
                 [by unfold_gen; try_solve | by repeat discr_or_first]).
 -  Opaque mult choose.
   case: instr => [r1 r2 | r1 r2 | r | r1 r2 r3 | | r1 r2 r3 | r1 r2 r3 |
                    l r | | z r | bop r1 r2 r3 | r | z r | r1 r2 | r1 r2 |
                    r1 r2 r3 | r1 r2 r3 | r | | r1 r2 | r1 r2];
                   move => H; apply frequency_equiv; left;
    instantiate_exists; try rewrite /gen_from_lengt; try by try_solve2.
    + rewrite liftGen2_def. eexists. split; [| try_solve2].
      by rewrite gen_label_correct.
    + rewrite liftGen2_def. eexists. split; [| try_solve2].
      rewrite /arbitrary /arbInt. by apply arbInt_correct.
Qed.
*)

(* Proofs for variations *)

(* Vary Atom *)
Lemma gen_vary_atom_correct :
  forall (l : Label) (a : Atom),
    let 'v @ la := a in
    val_spec v ->
    semGenSize (gen_vary_atom l inf a) size <--> (fun a' =>
                                    let 'v' @ la' := a' in
                                    indist l a a' /\ val_spec v').
Proof.
  move=> l a. case: a => va la.
  move=> Hspec; case => va' la'.
  rewrite /gen_vary_atom /indist /indistAtom.
  case: (isLow la l).
  + (* la lower that observability level *)
    split.
    * (* Correctness *)
      move => /semReturnSize [Heq1 Heq2]; subst.
      split => //. apply/andP; split => //.
      apply/orP. right. rewrite /indist /indistValue /val_spec in Hspec *.
      case: va' Hspec => [i' | Ptr' | lv'] Hspec; by [].

    * (* Completeness *)
      move=> [/andP [/andP [Hflows1 Hflows2] /orP [H1 //= | H1]] H2].
      rewrite /indist /indistValue in H1. apply semReturnSize. 
      move: (flows_antisymm _ _ Hflows2 Hflows1) => Heq; subst.
      case: va Hspec H1 H2 => [i | ptr | lv];
      case: va' => [i' | ptr' | lv'] => // Hspec H1 H2; 
      unfold eq_op in H1;
      rewrite /eqP /= in H1 => /=;
      unfold eq_op in H1;                        
      rewrite /eqP /= in H1 => /=.
      - apply Z.eqb_eq in H1; by subst .
      - by destruct ptr.
      - destruct ptr; destruct ptr'.
        move:H1 => /andP [Hf1 Hf2].
        apply Z.eqb_eq in Hf2.
        unfold mframe_eq in Hf1. 
        case: (Mem.EqDec_block fp fp0) Hf1 => //=.
        rewrite /equiv.    
        by move => Heq _; subst.
      - by destruct ptr.
      - unfold label_eqb in H1.
        move/andP : H1 => [Hl1 Hl2].
        by move: (flows_antisymm _ _ Hl1 Hl2) => Heq; subst.
  + (* la higher than observable state *)
    split.
    * (* Correctness *)
      move => /semFrequencySize /=.
      case: va Hspec=> [i | ptr | lv];  case: va' => [i' | ptr' | lv'];
      move => Hpec [[freq g] [Hgen Hret]];
      case: Hgen => [[] *| [[]* | //]]; subst;
      simpl in Hret;
      try solve [
        apply semBindSize in Hret;
        move: Hret => [val [Heq1 Heq2]];
        apply gen_value_correct in Heq1;
        apply semReturnSize in Heq2;
        inversion Heq2; subst;
        by split; [ apply /andP; split => // | ]
      ];
      try solve [
        apply semLiftGen2Size in Hret;
        move: Hret => [[val lab] [[H1 H2] Heq2]];
        apply semLiftGenSize in H1;
        apply semReturnSize in H2;
        case: H1 => [x [H3 H4]];
        inv H4; inv Heq2; inv H2; inv H;
        try apply gen_int_correct in H3;
        try apply gen_pointer_correct in H3;
        try apply gen_label_correct in H3;
        simpl in *; subst;
        by split; [apply/andP; split => //= | ]
      ].
    * (* Completeness *)
      move=> [/andP[/andP [H1 H2] /orP [_| H3]]   H];
      apply semFrequencySize => //=;
      eexists; split;
      [ by left |  | by left | ]; 
        simpl; apply semBindSize;
        exists va'; split => //.
      - by apply gen_value_correct.
      - apply semReturnSize; by move: (flows_antisymm _ _ H2 H1) => Heq; subst.
      - by apply gen_value_correct.
      - apply semReturnSize; by move: (flows_antisymm _ _ H2 H1) => Heq; subst.
Qed.

(* Vary Ptr_atom *)
Lemma gen_vary_pc_correct:
  forall (obs: Label) (pc : Ptr_atom),
    (pc_in_bounds pc) ->
    semGenSize (gen_vary_pc obs inf pc) size <--> 
    (fun pc' => (if isLow ∂pc obs then pc == pc' else isHigh ∂pc' obs) /\ pc_in_bounds pc').
Proof.
  move => obs [pc_a pc_l] Hspec pc'.
  rewrite /gen_vary_pc /pc_lab.
  remember (flows pc_l obs) as Flows.
  destruct Flows.
  - split.
    + move => /semReturnSize H.
      inv H.
      by split.
    + move => [H1 H2].
      apply semReturnSize.
      by move: H1 => /eqP ->.
  - split.     
    + move => /semBindSize [xa [/gen_from_length_correct H1 H2]].
      move: H2 => /semBindSize [xl [/gen_high_label_correct H3 /semReturnSize H4]].
      apply H1 in code_len_correct; clear H1; rename code_len_correct into H1.
      rewrite /negb in HeqFlows.
      assert (isHigh pc_l obs) by by (rewrite /negb; rewrite <- HeqFlows).
      apply existsHighObsLow in H.
      apply H3 in H.
      inv H4.
      split => //=.
    + move => [H1 H2].
      apply semBindSize.
      destruct pc' as [xa xl] eqn:PC.
      exists xa; split.
      * by apply gen_from_length_correct.
      * apply semBindSize.
        exists xl; split => //=.
        - apply gen_high_label_correct => //.
          by apply (existsHighObsLow xl).
        - by apply semReturnSize.
Qed.          

Lemma gen_vary_regSet_correct:
  forall regs obs,
    (regs_spec regs)->
    semGenSize (sequenceGen (map (@smart_vary _ (smart_vary_atom) obs inf) regs)) size <-->
    (fun regs' =>
       regs_spec regs' /\ indist obs regs regs').
Proof.
  Opaque gen_vary_atom.
  move => regs obs [Hlen Hspec] regs'. split.
  - (* Correctness *)
    move => /semSequenceGenSize [Hlen' HIn].
    rewrite /indist /indistList.
    split.
    + (* regs_spec *)
      rewrite /regs_spec. split.
      * by rewrite Hlen' map_length.
      * move=> [vr' lr'] HIn'. move: (HIn') => HIn''.
        apply in_split in HIn''. move : HIn'' => [l1 [l2 Heq]].
        case: regs Hlen Hspec Hlen' HIn.
        - subst regs'. move=> _ _ Hlen' _.
          rewrite app_length /= in Hlen'. omega.
        - move => regsf regst. set regs := regsf :: regst.
          move=> Hlen Hspec Hlen' HIn.
          remember (List.nth (length l1) regs regsf) as r1.
          case: r1 Heqr1 => vr lr Heqr1.
          have/in_zip_swap Hzip : In (vr @ lr, vr' @ lr') (seq.zip regs regs').
          { apply in_nth_iff. exists (length l1). split.
            rewrite -nth_seqnth seq.nth_zip.
            rewrite Heq !nth_seqnth app_nth2 // minus_diag.
            rewrite (nth_foralldef _ _ _ (vr @ lr)) in Heqr1.
            by rewrite -Heqr1.
            rewrite map_length in Hlen'. rewrite -Hlen' Heq app_length.
            simpl. apply/ltP.
            rewrite -[X in (_ + X)%coq_nat]addn1 [X in (X < _)%coq_nat]plus_n_O.
            apply plus_lt_compat_l. apply/leP. rewrite addn_gt0.
            apply/orP; by right.
            rewrite !size_length. by rewrite map_length in Hlen'.
            rewrite -!size_length seq.size2_zip Heq seq.size_cat.
            rewrite -[X in X < _] addn0 ltn_add2l /= -[X in _ < X]addn1 addn_gt0.
            by apply/orP; right.
            rewrite map_length -!size_length in Hlen'.
            by rewrite -seq.size_cat -Hlen' Heq. }
          have Hind: In (vr' @ lr', (@smart_vary _ smart_vary_atom obs inf) (vr @ lr))
                 (seq.zip regs' (map (@smart_vary  _ smart_vary_atom  obs inf) regs))
            by apply in_map_zip.
          simpl in Hind. apply in_zip in Hzip.
          move : Hzip => [HIn1 /Hspec Hval] //.
          apply (Forall2_combine _ _ _ HIn _) in Hind.
          move/(gen_vary_atom_correct _ (vr @ lr) Hval) : Hind => [Hind Hval'].
          rewrite /indist /indistAtom in Hind.
          move/andP: Hind => [/andP [Hle1 Hle2] _].
            by have -> : lr' = lr by apply/flows_antisymm.
    + (* indist *)
      apply forallb2_forall. split.
      by rewrite map_length in Hlen'.
      move=> r r' /in_zip_swap Hzip. move: (Hzip) => HIn'.
      apply in_zip in HIn'. move: HIn' => [HIn1 HIn2].
      apply in_map_zip with (f := (@smart_vary _ smart_vary_atom obs inf))
        in Hzip. 
      apply (Forall2_combine _ _ _ HIn _) in Hzip.
      move: r r' HIn1 HIn2 Hzip => [vr lr] [vr' lr']  HIn1 /Hspec Hval.
      by move/(gen_vary_atom_correct obs (vr @ lr) Hval) => [H _].
  - rewrite /regs_spec /indist /indistList.
    move => [[Hlen' Hreg] /forallb2_forall [Hlen'' Hind]]. apply semSequenceGenSize.
    split. by rewrite map_length.
    apply seqzip__Forall2.
    + by rewrite map_length Hlen Hlen'.
    + move => [[vr' lr'] gen] /in_map_zip_iff
              [[vr lr] [Heq  HIn]] /=; subst.
      move : (HIn) => /in_zip_swap/Hind Hind'.
      apply in_zip in HIn. move : HIn => [HIn1 HIn2].
      rewrite /smart_vary /smart_vary_atom.
      move : (Hspec (vr @ lr) HIn2) => Hval.
      apply/ (gen_vary_atom_correct obs (vr @ lr) Hval).  split => //.
      by move : (Hreg (vr' @ lr') HIn1) => ?.
Qed.

Lemma Forall2_in_right : forall {A B} (l : list A) (l' : list B) f,
  Forall2 f l l' ->
  forall a', In a' l' -> 
               exists a, In a l /\ f a a'.
move => A B l l' f Hforall.
induction Hforall as [ | x x' l l' Hfxx Hforall IH].
- move => ? HIn; inv HIn.
- move => a' HIn.
  case: HIn => [Hleft | Hright].
  + subst.
    exists x.
    split => //=.
    by left.
  + pose proof IH a' as H.
    apply H in Hright; clear H.
    move: Hright => [a [HIn Hf]].
    exists a; split => //=.
    by right.
Qed.

Lemma Forall2_reg_aux : forall regs regs' reg' obs,
  Forall2 (fun (y : G register) (x : register) => semGenSize y size x)
          (map (gen_vary_atom obs inf) regs) regs' -> 
  In reg' regs' ->
  exists reg, In reg regs /\ semGenSize (gen_vary_atom obs inf reg) size reg'.
move => regs regs' reg' obs Hforall HIn.
pose proof (Forall2_in_right (map (gen_vary_atom obs inf) regs) regs' 
                             (fun (y : G register) (x : register) => semGenSize y size x) 
                             Hforall reg' HIn) as H.
move : H => [a [HIn' Hf]].
apply in_map_iff in HIn'.
move : HIn' => [reg [Hgen HIn'']]; subst.
exists reg; split => //=.
Qed.

  Opaque indist join flows gen_vary_atom.
Lemma gen_vary_stack_loc_correct : forall obs loc,
   (stack_loc_spec loc) ->
   semGenSize (gen_vary_stack_loc obs inf loc) size <-->
              (fun loc' => stack_loc_spec loc'  /\
                           if isLow (pc_lab (sf_return_addr loc)) obs
                           then indistLowStackFrame obs loc loc'
                           else isHigh (pc_lab (sf_return_addr loc')) obs).
Opaque gen_vary_pc gen_label gen_from_nat_length.
rewrite /stack_loc_spec /gen_vary_stack_loc.
move => obs [[pc_addr pc_lab] regs ptr_r lab] [Hregs [Hptr [Haddr Hg]]] loc'.
split; simpl.
+ destruct (isLow pc_lab obs) eqn:Flows.
  * {
    move => /semBindSize [regs' [/semSequenceGenSize [Hlen Hforall]
                                 /semReturnSize H2]].  
    inv H2.
    repeat split => //=.
    - rewrite map_length in Hlen.
      rewrite /regs_spec in Hregs.
      move: Hregs => [Hlen' _].
      by rewrite Hlen.
    - move => reg' HIn'.
      rewrite /regs_spec in Hregs.
      move: Hregs => [Hlen' Hreg].
      apply (Forall2_reg_aux _ _ reg' _) in Hforall => //=.
      move: Hforall => [reg [HIn Hsem]].
      pose proof (Hreg reg HIn) as AtomSpec.
      rewrite /atom_spec in AtomSpec.
      destruct reg eqn:Reg.
      pose proof (gen_vary_atom_correct obs (v @ l)).  
      simpl in H.
      apply H in AtomSpec; clear H.
      apply AtomSpec in Hsem; clear AtomSpec.
      rewrite /atom_spec.
      destruct reg' eqn:Reg'.
      by move: Hsem => [_ Hspec].
    - rewrite /indist /indistLowStackFrame.
      apply /andP; split => //=.
      apply /andP; split => //=.
      apply /andP; split => //=.
      rewrite /indist /indistList.
      apply forallb2_forall.
      split.
      + by rewrite map_length in Hlen.
      + move => reg reg' HIn.
        have H : In (reg', gen_vary_atom obs inf reg)
                    (seq.zip regs' (map (@gen_vary_atom obs inf) regs))
           by apply/in_map_zip/in_zip_swap.
        apply (Forall2_combine _ _ _ Hforall _) in H.
        simpl in H.
        destruct reg eqn:Reg.
        pose proof (gen_vary_atom_correct obs (v @ l)).  
        simpl in H0.
        rewrite /regs_spec in Hregs.
        move : Hregs => [? Hspec].
        apply in_zip in HIn.
        move : HIn => [HIn ?].
        rewrite -Reg in HIn.
        pose proof (Hspec reg HIn) as H'.
        rewrite /atom_spec in H'.
        rewrite Reg in H'.
        apply H0 in H'; clear H0.
        apply H' in H; clear H'.
        destruct reg'; subst.
        by move : H => [? _].
  }
  * {
    move => /semBindSize [regs' [/semVectorOfSize [HLen' Hregs'] 
                                 /semBindSize [pc' [Hpc'
                                 /semBindSize [lab' [Hlab 
                                 /semBindSize [ptr_r' [Hptr' 
                                 /semReturnSize H]]
                          ]]]]]].
    inv H.
    apply gen_vary_pc_correct in Hpc'.
    rewrite Flows in Hpc'.
    apply gen_from_nat_length_correct in Hptr'.
    repeat split => //=.
    + move => reg' HIn'.
      rewrite /set_incl in Hregs'.
      apply Hregs' in HIn'.
      by apply gen_atom_correct in HIn'.
    + destruct pc' eqn:PC'.
      by move : Hpc' => [_ ?].
    + move: Hpc' => [Flows' Hpc'].
      rewrite /negb in Flows'.
      destruct (isLow ∂(pc') obs) eqn:Flows'' => //=.
    + apply no_regs_positive.
    + by split.
  }
+ move: loc' => [[pc_addr' pc_lab'] regs' ptr_r' lab'].
  simpl in *.
  move => [[[Hlen' Hregs'] [Hvalid Haddr']] Hindist].
  destruct (isLow pc_lab obs) eqn:Flows.
  * {
    apply semBindSize.
    exists regs'; split.
    - apply semSequenceGenSize; split.
      rewrite map_length.
      rewrite /regs_spec in Hregs.
      by move : Hregs => [-> _].
    - { 
      apply seqzip__Forall2.
      + rewrite map_length.
        rewrite /regs_spec in Hregs.
        move : Hregs => [-> _]. 
        by apply /eqP.
      + move => [reg' g] HIn //=.
        apply in_map_zip_iff in HIn.
        move : HIn => [reg [Hgen HIn]].
        subst.
        pose proof (gen_vary_atom_correct obs reg).
        destruct reg eqn:Reg.
        move : (HIn) => HInZip.
        apply in_zip in HIn.
        move : HIn =>  [HIn1 HIn2].
        rewrite /regs_spec in Hregs.
        move : Hregs => [Hlen Hregs].
        pose proof (Hregs (v @ l) HIn2) as Hspec.
        rewrite /atom_spec in Hspec.
        apply H in Hspec; clear H.
        apply Hspec.
        destruct reg' eqn:Reg'.
        * split => //=.
          subst.
          rewrite /indist /indistLowStackFrame in Hindist.
          move: Hindist => /andP [/andP [/andP [? Hindist] ?] ?].
          rewrite /indist /indistList in Hindist.
          apply forallb2_forall in Hindist.
          move:  Hindist => [? H].
          apply in_zip_swap in HInZip.
          by apply H in HInZip.
        * by apply Hregs' in HIn1.
    }
    - apply semReturnSize.
      rewrite /indist /indistLowStackFrame in Hindist.
      move: Hindist => /andP [/andP [/andP [/eqP Heq1 Hindist] /eqP Heq2] /eqP Heq3]; subst.
      by inv Heq1.
  }
  * apply semBindSize.
    exists regs'; split => //=.
    - apply semVectorOfSize; split => //=.
      move => reg' HIn'.
      apply gen_atom_correct.
      by apply Hregs'.
   apply semBindSize.
   exists (PAtm pc_addr' pc_lab'); split => //=.
   - apply gen_vary_pc_correct.
     + by rewrite /pc_in_bounds.
     + rewrite Flows; split => //=.
   apply semBindSize.
   exists lab'; split => //=.
   - apply gen_label_correct => //.
   apply semBindSize.                                
   exists ptr_r'; split => //=.
   - by apply gen_from_nat_length_correct.
   by apply semReturnSize.
Qed.   

Lemma gen_vary_stack_correct :
  forall (st : Stack) obs,
    stack_spec st ->
    semGenSize (gen_vary_stack obs inf st) size <--> 
    (fun st' => indist obs st st' /\ 
                stack_spec st' /\
                length (unStack st) = length (unStack st')).
Proof.
  move=> st obs Hspec st'.
  rewrite /stack_spec in Hspec.
  move : Hspec => [Heq | [loc [Heq Hspec]]].
 (* Stack empty *)
  - split.
    + inv Heq.
      rewrite /gen_vary_stack /gen_vary_low_stack.
      move => /semLiftGenSize H.
      inv H.
      move : H0 => [/= /semSequenceGenSize [len _] H].
      inv H.
      destruct x => //=.
      do 2 split => //=.
      by left.
    + inv Heq. 
      move => [H1 [H2 H3]].
      destruct st' => //=.
      rewrite /gen_vary_stack /gen_vary_low_stack.
      apply semLiftGenSize.
      simpl.
      destruct l => //=.
      eexists; split => //=.
      apply semSequenceGenSize.
      split => //=.
 (* Stack Singleton *)
  - inv Heq. split. 
    { 
    + rewrite /gen_vary_stack /gen_vary_low_stack.
      move => /semLiftGenSize /= [st'' [/semSequenceGenSize [Hlen Hforall] H2]]. 
      inv H2.
      destruct st'' eqn:EqST.
      * inv Hlen.
      * { repeat split => //=.
          + {
            inv Hlen.
            destruct l => //=.
            inv Hforall.           
            apply gen_vary_stack_loc_correct in H3 => //=.
            move : H3 => [? H].                                                        
            rewrite /indist /indistStack.
            rewrite /filterStack /stackFrameBelow.
            destruct loc eqn:Loc; destruct s eqn:S;
            destruct sf_return_addr0 eqn:Ret0;
            destruct sf_return_addr1 eqn:Ret1;
            simpl in *.
            destruct (isLow l obs) eqn:Flows.
            - { (* l <: obs *)
              simpl in H.
              move: H => /andP [/andP [/andP [/eqP Heq1 
                                            Hindist]
                                     /eqP Heq3]
                              /eqP Heq4]; subst.
              inv Heq1.
              apply forallb2_forall; split => //=.
              * by rewrite Flows.
              * move => x y /= HIn.
                rewrite Flows in HIn.
                simpl in HIn.
                case : HIn => [[] * | //=]; subst.
                rewrite /indistLowStackFrame Flows => //=.
                apply /andP; split => //=.
                apply /andP; split => //=.
                apply /andP; split => //=.                                        
              }
            - rewrite /negb in H.
              destruct (isLow l0 obs) eqn:Flows' => //=.
          }
          + rewrite /stack_spec. right.
            exists s; split => //=.
            * inv Hlen.
              destruct l => //=.
            * inv Hforall.
              inv H4.
              apply gen_vary_stack_loc_correct in H2 => //=.
              by move : H2 => [? _].        
        }
    }
    (* Completeness *)
    + Opaque indistLowStackFrame.
      move => [Hindist [Hspec' Hlen]].
      rewrite /gen_vary_stack /gen_vary_low_stack.
      apply semLiftGenSize.
      destruct st' as [st'].
      destruct st' as [ | loc' st'] => //=.              
      simpl in Hlen.
      inv Hlen.
      destruct st' => //=.
      exists [loc']; split => //=.
      apply semSequenceGenSize; split => //=.
      constructor => //=.
      apply gen_vary_stack_loc_correct => //=.
      split => //=.
      - rewrite /stack_spec in Hspec'.
        case : Hspec' => [// | [loc'' [Heq Hs]]].
        by inv Heq.
      - destruct loc; destruct loc'; 
        destruct sf_return_addr0; destruct sf_return_addr1; simpl in Hindist.
        destruct (isLow l obs) eqn:Flows.
        + { 
            rewrite /indist /indistStack in Hindist.
            apply forallb2_forall in Hindist.
            move: Hindist => [Hlen Hindist].
            rewrite /filterStack /stackFrameBelow in Hindist.
            simpl in *.
            rewrite Flows in Hindist.
            destruct (isLow l0 obs) eqn:Flows'.
            * rewrite Flows.                                                
              apply Hindist => //=.
              by left.
            * rewrite Flows.
              apply Hindist => //=.
              rewrite /filterStack /stackFrameBelow in Hlen.
              simpl in Hlen.
              rewrite Flows Flows' in Hlen.
              inv Hlen.
          }
       + rewrite Flows.
         rewrite /indist /indistStack in Hindist.
         apply forallb2_forall in Hindist.
         move : Hindist => [Hlen Hindist]. 
         rewrite /filterStack /stackFrameBelow in Hlen.
         simpl in *.
         destruct (isLow l0 obs) eqn:Flows' => //=.
         rewrite Flows in Hlen.
         inv Hlen.
Qed.

(* Vary Memory *)

Definition frame_spec (fr : frame) :=
  let 'Fr _ _ data := fr in
      (forall a, In a data -> atom_spec a).

Lemma gen_vary_frame_correct :
  forall obs fr,
    (frame_spec fr) ->
    semGenSize (gen_var_frame obs inf fr) size <-->
    (fun fr' => indist obs fr fr' /\
     (frame_spec fr') /\
     let 'Fr _ _ data := fr in
     let 'Fr _ _ data' := fr' in
     length data <= length data' <= (length data) + 1).
Proof.
  move => obs [stamp label data] HforallIn
              [stamp' label' data'].
  Opaque indist join flows gen_vary_atom.
  split.
  { rewrite /gen_var_frame /indist /indistFrame.
    destruct (isLow stamp obs) eqn:Flows.
    - (* stamp <: obs *)
      simpl in *.
      destruct (isLow label obs) eqn:Flows'.
      { (* label <: obs *)
        simpl in *.
        move: (join_minimal stamp label obs Flows Flows') => Hjoin.
        rewrite Hjoin /=.
        move => /semBindSize [data'' [/semSequenceGenSize [Hlen Hforall] 
                                      /semReturnSize [eq1 eq2 eq3]]]; subst.
        rewrite map_length in Hlen. rewrite Flows.
        have Hindist_spec:
          (forall x y : Atom,
             In (x, y) (seq.zip data data') ->
             indist obs x y = true /\ atom_spec y).
          { move => [v1 l1] [v2 l2] HIn. apply in_zip_swap in HIn.
            move: (HIn) => HIn'. apply in_zip in HIn'. 
            move: HIn' => [HIn1 Hval]. apply HforallIn in Hval.
            move : (Hval) => /(gen_vary_atom_correct obs (v1 @ l1)) Hequiv.
            apply in_map_zip with (f := (@gen_vary_atom obs inf)) in HIn.
            move: (HIn) => HIn'. apply in_zip in HIn.
            apply (Forall2_combine _ _ _ Hforall _) in HIn'.
            simpl in HIn'.
            apply Hequiv in HIn'.
            case : HIn' => [Hindist Hspec].
            by split => //.
          }
          repeat (split => //; try apply/andP);
            try (try apply/leP; omega); try by apply flows_refl.
          - rewrite /indist /indistList.
            apply forallb2_forall => //. split => //.
            by move => x y /Hindist_spec [Hind _].
          - move => [v2 l2] HIn2.
            move : (HIn2) => HIn2'. apply in_split in HIn2'.
            move : HIn2' => [data'_pre [data'_post Heq]].
            destruct data as [|data_hd data_tl].
            + rewrite Heq in Hlen.  rewrite app_length /= in Hlen. omega.
            + remember (data_hd :: data_tl) as data. clear Heqdata.
              remember (List.nth (length data'_pre) data data_hd) as y.
              destruct y as [v1 l1].
              have/Hindist_spec [_ Hspec] :
                In (v1 @ l1, v2 @ l2) (seq.zip data data').
              { apply in_nth_iff. exists (length data'_pre). split.
                - rewrite -nth_seqnth seq.nth_zip //.
                  * rewrite Heq !nth_seqnth app_nth2 // minus_diag.
                    rewrite (nth_foralldef _ _ _ (v1 @ l1)) in Heqy.
                      by rewrite -Heqy.
                  * rewrite -Hlen Heq app_length. apply/ltP.
                    apply NPeano.Nat.lt_add_pos_r. simpl. omega.
                - rewrite zip_combine // combine_length Hlen NPeano.Nat.min_id.
                  rewrite -Hlen Heq app_length. apply/ltP.
                  apply NPeano.Nat.lt_add_pos_r. simpl. omega. }
              assumption.
            + rewrite Hlen. by apply leq_addr. }
        { (* label <: obs = false *)
          apply Bool.negb_true_iff in Flows'.
          move/(join_equiv stamp label obs Flows) : Flows' => Hjoin.
          rewrite Hjoin.
          move => /semBindSize [data'' [/semBindSize [len [/semChooseSize Hchoose
                                                           /semVectorOfSize [Hlen Hforall]]] 
                                         /semReturnSize [eq1 eq2 eq3]]]; subst.
          assert (H : Random.leq (length data) (length data).+1).
          { 
            rewrite /Random.leq.
            simpl.
            apply/leP.
            apply le_n_Sn.
          } 
          apply Hchoose in H; clear Hchoose; rename H into Hchoose.
          move: Hchoose => /andP [Hle3 Hle4].
          simpl in Hle3, Hle4. rewrite Flows.
          repeat (split => //; try apply/andP); (try by rewrite addn1); 
          try by apply flows_refl.
          by move => a /Hforall/gen_atom_correct Hin. }
    - (* stamp <: obs = false *)
        simpl in *. remember (label <: obs) as Flows''.
        move => /semBindSize [lab [? /semBindSize [data'' 
                                                     [/semBindSize [len [/semChooseSize H 
                                                                         /semVectorOfSize 
                                                                   [Hlen HforallIn']]]
                                                      /semReturnSize [eq1 eq2 eq3]
                             ]]]]; subst.
          assert (Hchoose : Random.leq (length data) (length data).+1).
          { 
            rewrite /Random.leq.
            simpl.
            apply/leP.
            apply le_n_Sn.
          } 
          apply H in Hchoose; clear H.
          move: Hchoose => /andP [Hle3 Hle4]. simpl in *.
        repeat (split => //; try apply/andP); (try by rewrite addn1); 
          try by apply flows_refl.
        by move => a /HforallIn'; apply gen_atom_correct. }
  { rewrite /indist /indistFrame /frame_spec /gen_var_frame.
    remember (@flows Lab4 _ stamp obs) as b. destruct b; simpl in *;
    remember (@flows Lab4 _ stamp' obs) as b'; destruct b'; simpl in *;
    try (move: Hindist => /andP [Hl1 Hl2];
         move: (flows_antisymm _ _ Hl1 Hl2) => Heq; congruence).
    - move=> [/andP [/eqP H1 H2] [H3 H4]].
      subst.
      symmetry in Heqb.
      rewrite Bool.andb_if in H2.
      rewrite Heqb in H2.
      move : H2 => /andP [/eqP H1 H2]; subst.
(*       move: (flows_antisymm _ _ Hl1 Hl2) => Heq {Hl1 Hl2}; subst.
      move: (flows_antisymm _ _ Hl3 Hl4) => Heq {Hl3 Hl4}; subst. *)
      remember (flows label' obs) as b''; destruct b''; simpl in *;
      symmetry in Heqb''. 
      + (* label' <: obs = true *)
        { 
        rewrite Heqb; simpl.
        rewrite (join_minimal _ _ _ Heqb Heqb'') /=.
        apply semBindSize.
        exists data'. split => //. apply semSequenceGenSize.
        rewrite /indist /indistList in H2.
        move : H2 => /forallb2_forall [Hlen' HforallIn'].
        split => //.
        * by rewrite map_length. 
        * apply seqzip__Forall2.
          - rewrite map_length. by rewrite Hlen'.
          - move => [a ga] /in_map_zip_iff [[v l] [Heq HIn]].
            simpl in *.
            move: (HIn) => /in_zip_swap/HforallIn' HInzip.
            apply in_zip in HIn. move : HIn => [HIn1 /HforallIn Hval].
            subst.
            apply (gen_vary_atom_correct obs (v @ l) Hval). 
            destruct a eqn:A.
            split => //.
            apply H3 in HIn1.
            by rewrite /atom_spec in HIn1.
        * by apply semReturnSize.
        } 
      + { 
        rewrite (not_flows_not_join_flows_right _ _ _ Heqb'') /=.
        rewrite Heqb; simpl.
        apply semBindSize.
        exists data'. split => //. 
        apply semBindSize.
        exists (length data'); split.
        * apply semChooseSize. 
          - rewrite /Random.leq.
            simpl.
            apply/leP.
            apply le_n_Sn.
          - move : H4 => /andP [Hle1 Hle2].
            simpl => //. apply /andP. split => //=. 
            by rewrite -addn1.
        * apply semVectorOfSize. split => //.
          move => a Hin.
          apply /gen_atom_correct.
          by apply H3.
        * by apply semReturnSize.
        }
    - move=> [/andP [/eqP Hl1 Hl2] _].
      symmetry in Heqb, Heqb'.
      subst; congruence.
    - move=> [/andP [/eqP Hl1 Hl2] _]; subst.
      subst; congruence.
    - move=> [/andP [/eqP Hl1 Hl2] [Hforall /andP [Hle1 Hle2]]]; subst.
      symmetry in Heqb.
      rewrite Heqb; simpl.
      apply semBindSize.
      exists label'. split; [by apply gen_label_correct |].
      apply semBindSize.
      exists data'. split => //=.
      + apply semBindSize.
        exists (length data'). split.
        * apply semChooseSize. simpl. 
          apply /leP; omega.
        * apply /andP. split => //. by rewrite -addn1.
        * apply semVectorOfSize. split => //.
          by move => a /Hforall/gen_atom_correct HIn. 
          by apply semReturnSize.
      }
Qed.

(*
Definition frame_spec (fr : frame) :=
  let 'Fr _ _ data := fr in
      (forall a, In a data -> atom_spec a).

Lemma gen_vary_frame_correct :
  forall obs fr,
    (frame_spec fr) ->
    semGenSize (gen_var_frame obs inf fr) size <-->
    (fun fr' => indist obs fr fr' /\
     (frame_spec fr') /\
     let 'Fr _ _ data := fr in
     let 'Fr _ _ data' := fr' in
     length data <= length data' <= (length data) + 1).
*)

Definition mem_spec (m : memory) := 
  forall mf l st data,
    Mem.get_frame m mf = Some (Fr st l data) ->
    (C.min_frame_size <= Z.of_nat (length data) <= C.max_frame_size)%Z /\
    (forall a, In a data -> atom_spec a) /\
    st = ⊥ /\ Mem.stamp mf = ⊥.

Lemma handle_single_mframe_correct : 
  forall obs m mf fr,
    mem_spec m ->
    Mem.get_frame m mf = Some fr -> 
    semGenSize (handle_single_mframe obs inf m mf) size <-->
    (fun m' => 
       forall mf', 
         if Mem.EqDec_block mf mf' then
           exists fr', Mem.get_frame m' mf = Some fr' /\
                       indist obs fr fr' /\
                       (frame_spec fr') /\
                       let 'Fr _ _ data := fr in
                       let 'Fr _ _ data' := fr' in
                       length data <= length data' <= (length data) + 1 
         else Mem.get_frame m' mf' = Mem.get_frame m mf').
Proof. 
move => obs m mf fr HmemSpec Hfr m'.
split.                                                   
+ {
  rewrite /handle_single_mframe.
  rewrite Hfr.
  move => /semBindSize [fr' [Hfr' H]].
  pose proof (Mem.upd_get_frame _ _ _ m mf fr fr' Hfr) as Hm'.
  move: Hm' => [m'' Hm''].
  rewrite Hm'' in H.
  apply semReturnSize in H.
  inv H.
  rewrite /smart_vary /smart_vary_frame in Hfr'.
  apply gen_vary_frame_correct in Hfr'.
  move : Hfr' => [Hindist [Hspec Hlen]].
  destruct fr eqn:EqFr; destruct fr' eqn:EqFr'.
  move => mf'.
  destruct (Mem.EqDec_block mf mf') eqn:HEqB.
  - simpl.
    move: (e) => e'.
    rewrite /equiv in e'.
    exists (Fr stamp0 label0 l0).
    split => //=.
    have : (Mem.upd_frame m mf (Fr stamp0 label0 l0) = Some m') by subst.
    move => Hm.
    pose proof (Mem.get_upd_frame _ _ _ m m' mf _ Hm mf') as H.
    rewrite /equiv_dec in H.  
    rewrite HEqB in H.
    by subst.
  - simpl.
    have : (Mem.upd_frame m mf (Fr stamp0 label0 l0) = Some m') by subst.
    move => Hm.
    pose proof (Mem.get_upd_frame _ _ _ m m' mf _ Hm mf') as H.
    rewrite /equiv_dec in H.  
    rewrite HEqB in H.
    by subst.
  rewrite /mem_spec in HmemSpec.    
  destruct fr.
  pose proof (HmemSpec mf label stamp l Hfr) as H; clear HmemSpec.
  by move : H => [_ [? _]].
}
+ move => H.
  rewrite /handle_single_mframe Hfr.
  apply semBindSize.
  pose proof (H mf) as Hyp.
  (* I'm not sure how to prove something this obvioues *)
  have : (Mem.EqDec_block mf mf) by admit. 
  move => EqDec.
  rewrite EqDec in Hyp.
  move : Hyp => [fr' [Hget [Hindist [Hfr' Hlen]]]].
  exists fr'.
  split => //=.
  - apply gen_vary_frame_correct.
    rewrite /mem_spec in HmemSpec.
    destruct fr; destruct fr'.
    pose proof (HmemSpec _ _ _ _ Hfr) as H'.
    by move : H' => [_ [? _]].
  - split => //=.
    pose proof (Mem.upd_get_frame _ _ _ m mf fr fr' Hfr) as Hm'.
    move : Hm' => [m'' Hm''].
    rewrite Hm''.
    
    have : (forall block, Mem.get_frame m' block = Mem.get_frame m'' block).
    { 
      move => block.
      destruct (Mem.EqDec_block mf block) eqn:EqB.
      + pose proof (H block) as Hb.
        rewrite EqB in Hb. simpl in Hb.
        move: (e) => e'.
        rewrite /equiv in e'.
        subst.
        pose proof (Mem.get_upd_frame _ _ _ _ _ _ _ Hm'' block) as Hyp.
        rewrite /equiv_dec EqB in Hyp.
        by rewrite Hyp Hget.
      + pose proof (H block) as Hb.
        rewrite EqB in Hb; simpl in Hb.
        pose proof (Mem.get_upd_frame _ _ _ _ _ _ _ Hm'' block) as Hyp.
        rewrite /equiv_dec EqB in Hyp.
        by rewrite Hb Hyp.
    }
    move => MemExt.
    
    pose proof (Mem.memory_extensionality m' m'' MemExt).
    subst.
    by apply semReturnSize.
Qed.    

Lemma foldr_handle : 
  forall obs m mf fr m',
    mem_spec m ->
    Mem.get_frame m mf = Some fr -> 
    seq.foldr (fun (b : mframe) (p : memory -> Prop) (m0 : memory) =>
                 exists (m' : memory),
                   (semGenSize (handle_single_mframe obs inf m0 b) size :&: p) m')
              [set m'] (Mem.get_blocks elems m) m ->
    mem_spec m'.
Proof.
move => obs m mf fr m' Hspec Hget Hfoldr.
induction (Mem.get_blocks elems m).

seq.foldr (fun 

*)
Lemma gen_vary_memory_correct:
  forall (obs: Label) (m : memory),
    (mem_spec m) ->
    semGenSize (gen_vary_memory obs inf m) size <--> 
    (fun m' => indist obs m m' /\ mem_spec m').
Proof. 
move => obs m Hspec m'.
rewrite /indist /indistMem /blocks_stamped_below /allThingsBelow.
split.
- {
    rewrite /gen_vary_memory.
    move => /semFoldGen_right H.
    

    apply semFoldGen_right.
Qed.


(* Main theorem *)

Lemma combine_l : forall {A} (l : list A) x y,
                    In (x, y) (combine l l) -> x = y.
Proof. admit. Qed.

Require Import ZArith.

Lemma gen_variation_state_correct :
  gen_variation_state <--> (fun b =>
                              let '(Var l s1 s2) := b in
                              indist l s1 s2 = true).
Proof.
  (* The statement is not complete as we need the states to satisfy
     some validity requirements *)
Abort.
  (* case => Lab s1 s2. split. rewrite /gen_variation_state.  *)
  (* rewrite bindGen_def.  *)
  (* move => [l1 [Htop H]].  *)
  (* rewrite bindGen_def in H.  *)
  (* move: H => [[mem mframes] [Hinit H]].  *)
  (* case: mframes Hinit H => [ | mframe1 mframes] Hinit H. *)
  (* - rewrite returnGen_def /= in H.  *)
  (*   move : H => [Heq1 Heq2 Heq3]. subst.  *)
  (*   rewrite /indist /indistState /failed_state !trace_axiom //=. *)
  (*   rewrite /label_eq /isHigh /isLow /flows. simpl.  *)
  (*   have Ht: Zset.incl Zset.empty Zset.empty = true by *)
  (*       apply/Zset.incl_spec; rewrite Zset.elements_empty.  *)
  (*   rewrite Ht -beq_nat_refl /indistMemHelper.  *)
  (*   simpl. by rewrite forallb_indist. *)
  (* - case : mframe1 Hinit H => mf1 Z1 Hinit H1. *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ptr_a [sgen H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [regset [sgen2 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [st [sgen3 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [memg [sgen4 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [instr [sgen5 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [lab [sgen6 H1]].  *)
  (*   rewrite bindGen_def in H1. *)
  (*   move:  H1 => [ST' [sgen7 H1]].      *)
  (*   rewrite returnGen_def in H1. *)
  (*   move : H1 => [Heq1 Heq2 Heq3]; subst. *)
  (*   rewrite /smart_gen in sgen, sgen2, sgen3, sgen4, sgen5, sgen6, sgen7 . *)

End WithDataLenNonEmpty.
