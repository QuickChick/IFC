Require Import Coq.Strings.String.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import finset path fingraph. (* These depend on Mathematical Components 1.5
                      http://www.msr-inria.fr/projects/mathematical-components-2/ *)

Require Import Utils Labels Rules Memory Instructions Machine Indist NotionsOfNI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Module NIProof (Lattice : FINLAT).

Module GenericMachine := MachineM Lattice.
Export GenericMachine.

Module GenericIndist := IndistM Lattice.
Export GenericIndist.


(* Interface with non-ssr definitions *)
Lemma replicateE T (a : T) n : replicate a n = nseq n a.
Proof.
by elim: n=> //= n ->.
Qed.

Definition def_atom := Vint 0 @ ⊥.

Lemma nth_errorE T l n (a def : T) : List.nth_error l n = Some a ->
  nth def l n = a /\ n < size l.
Proof.
by elim: l n => [[]|x l IHl [[->]|]].
Qed.

Lemma nth_error_ZE T l n (a def : T) : nth_error_Z l n = Some a ->
  nth def l (BinInt.Z.to_nat n) = a /\ BinInt.Z.to_nat n < size l.
Proof.
by rewrite /nth_error_Z; case: (BinInt.Z.ltb n 0) => //; apply: nth_errorE.
Qed.

Lemma update_listE T r r' (def : T) rk a : update_list r rk a = Some r' ->
  r' = set_nth def r rk a /\ rk < size r.
Proof.
elim: r rk r' => // x l IHl [r' [<-]|rk] // [|y r'] /=.
  by case: (update_list l rk a)=> //.
case H: (update_list l rk a) => [a'|] //; case=> <- <-.
by split; case: (IHl rk a') => // <-.
Qed.

Lemma update_list_ZE r r' rk a : update_list_Z r rk a = Some r' ->
  r' = set_nth def_atom r (BinInt.Z.to_nat rk) a /\
  BinInt.Z.to_nat rk < size r.
Proof.
rewrite /update_list_Z; case: (BinInt.Z.ltb rk 0)=> //.
exact: update_listE.
Qed.

(* TODO: prove once mframe is actually made finite *)
Axiom f : mframe -> ordinal (2^32).
Axiom g : ordinal (2^32) -> mframe.
Axiom fgK : cancel f g.

Canonical label_eqType : eqType := Eval hnf in (@LabelEqType.label_eqType _ _).

Axiom label_choiceMixin : choiceMixin Label.
Canonical label_choiceType := Eval hnf in ChoiceType Label label_choiceMixin.

Axiom label_countMixin : Countable.mixin_of Label.
Canonical label_countType := Eval hnf in CountType Label label_countMixin.

(* TODO: prove using the assumptions in FINLAT *)
Axiom label_enumP : Finite.axiom (undup elems).

Definition label_finMixin := FinMixin label_enumP.
Canonical label_finType := Eval hnf in FinType Label label_finMixin.

Definition mframe_eqMixin := CanEqMixin fgK.
Canonical mframe_eqType := Eval hnf in EqType mframe mframe_eqMixin.

Definition mframe_choiceMixin := CanChoiceMixin fgK.
Canonical mframe_choiceType := Eval hnf in ChoiceType mframe mframe_choiceMixin.

Definition mframe_countMixin := CanCountMixin fgK.
Canonical mframe_countType := Eval hnf in CountType mframe mframe_countMixin.

Definition mframe_finMixin := CanFinMixin fgK.
Canonical mframe_finType := Eval hnf in FinType mframe mframe_finMixin.

Canonical block_eqType := Eval hnf in EqType (Mem.block Label) mframe_eqMixin.
Canonical block_choiceType := Eval hnf in ChoiceType (Mem.block Label) mframe_choiceMixin.
Canonical block_countType := Eval hnf in CountType (Mem.block Label) mframe_countMixin.
Canonical block_finType := Eval hnf in FinType (Mem.block Label) mframe_finMixin.

Definition is_low_pointer obs (a : Atom) : bool :=
  if a is Vptr p @ l then isLow l obs else false.

Definition extract_mframe (a : Atom) : option mframe :=
  if a is Vptr (Ptr fp _) @ _ then Some fp else None.

Definition mframes_from_atoms obs (atoms : list Atom) : {set mframe} :=
  [set t in pmap extract_mframe (filter (is_low_pointer obs) atoms)].

Lemma mframes_from_atoms_nth r r1 fp i lbl obs :
  registerContent r r1 = Some (Vptr (Ptr fp i) @ lbl) -> isLow lbl obs ->
  fp \in mframes_from_atoms obs r.
Proof.
case/(nth_error_ZE def_atom) => get_r1 lt_r1 low_lbl.
rewrite inE mem_pmap; apply/mapP.
exists (Vptr (Ptr fp i) @ lbl) => //.
by rewrite mem_filter /= low_lbl -get_r1 mem_nth.
Qed.

Lemma mem_set_nth (T : eqType) (x : T) x0 l i v :
  i < size l -> x \in set_nth x0 l i v ->
  x = v \/ x \in l.
Proof.
move=> /maxn_idPr eq_size /(nthP x0) [j].
rewrite nth_set_nth size_set_nth /= => lt_j <-.
have [_|_] := altP (j =P i); first by left.
by right; rewrite mem_nth // -eq_size.
Qed.

Lemma mframes_from_atoms_upd obs r rk r' atom :
  registerUpdate r rk atom = Some r' ->
  mframes_from_atoms obs r' \subset mframes_from_atoms obs r :|: mframes_from_atoms obs [:: atom].
Proof.
case/update_list_ZE => ->; set k := BinInt.Z.to_nat rk => lt_k.
rewrite /mframes_from_atoms; apply/subsetP=> x; rewrite !inE /= !mem_pmap.
case/mapP=> a; rewrite mem_filter; case/andP => low_pt.
move/(mem_set_nth lt_k)=> // [<- ->|a_in_r ->].
  by rewrite [X in _ || X]map_f ?orbT // low_pt inE.
by rewrite map_f // mem_filter low_pt.
Qed.

Arguments mframes_from_atoms_upd [obs r rk r' atom] _.

Fixpoint root_set_stack obs (s : list StackFrame) : {set mframe} :=
  match s with
    | nil => set0
    | (SF pc rs _ _) :: s' =>
      if isLow ∂pc obs then
        mframes_from_atoms obs rs :|: root_set_stack obs s'
      else root_set_stack obs s'
  end.

Definition root_set_registers obs (r : regSet) pcl :=
  if isLow pcl obs then mframes_from_atoms obs r
  else set0.

Lemma root_set_registers_nth r r1 fp i lbl obs pcl :
  registerContent r r1 = Some (Vptr (Ptr fp i) @ lbl) ->
  isLow pcl obs -> isLow lbl obs ->
  fp \in root_set_registers obs r pcl.
Proof.
move=> get_r1 low_pcl low_lbl; rewrite /root_set_registers low_pcl.
exact: (mframes_from_atoms_nth get_r1).
Qed.

Lemma root_set_registers_upd obs pcl r rk r' atom :
  registerUpdate r rk atom = Some r' ->
  root_set_registers obs r' pcl \subset root_set_registers obs r pcl :|: mframes_from_atoms obs [:: atom].
Proof.
rewrite /root_set_registers.
case: ifP => _; first exact: mframes_from_atoms_upd.
by rewrite sub0set.
Qed.

Arguments root_set_registers_upd [obs pcl r rk r' atom] _.

Lemma joinC : commutative join.
Proof.
move=> l1 l2.
by apply/flows_antisymm; rewrite join_minimal ?flows_join_left ?flows_join_right.
Qed.

Lemma flows_join l1 l2 l : flows (l1 \_/ l2) l = flows l1 l && flows l2 l.
Proof.
case Hl1: (flows l1 l).
  case Hl2: (flows l2 l).
    by rewrite (join_minimal _ _ _ Hl1 Hl2).
  by rewrite joinC (not_flows_not_join_flows_left _ _ _ Hl2).
by rewrite (not_flows_not_join_flows_left _ _ _ Hl1).
Qed.

Lemma low_join l1 l2 l : isLow (l1 \_/ l2) l = isLow l1 l && isLow l2 l.
Proof. exact: flows_join. Qed.

Lemma joinA : associative join.
Proof.
(* Cannot use wlog because of missing type class resolution *)
have: forall l1 l2 l3, l1 \_/ (l2 \_/ l3) <: (l1 \_/ l2) \_/ l3.
  move=> l1 l2 l3.
  rewrite flows_join.
  apply/andP; split; first exact/join_1/join_1/flows_refl.
  rewrite flows_join.
  apply/andP; split; first exact/join_1/join_2/flows_refl.
  exact/join_2/flows_refl.
move=> H l1 l2 l3.
apply/flows_antisymm; first exact:H.
rewrite [_ \_/ l3]joinC [l2 \_/ l3]joinC [l1 \_/ l2]joinC.
by rewrite [l1 \_/ (_ \_/ _)]joinC; apply: H.
Qed.

Lemma root_set_registers_join obs r l1 l2 :
  root_set_registers obs r (l1 \_/ l2) = root_set_registers obs r l1 :&: root_set_registers obs r l2.
Proof.
rewrite /root_set_registers /=.
rewrite low_join.
case: (isLow l1 obs); last by rewrite set0I.
case: (isLow l2 obs); first by rewrite setIid.
by rewrite setI0.
Qed.

Definition root_set obs (st : State) : {set mframe} :=
  let '(St _ _ s r pc) := st in
  root_set_registers obs r ∂pc :|: root_set_stack obs (unStack s).

Definition link obs (mem : memory) (f1 f2 : mframe) :=
  if Mem.get_frame mem f1 is Some (Fr l atoms) then
    isLow l obs && (f2 \in mframes_from_atoms obs atoms)
  else false.

Definition reachable obs (mem : memory) : rel mframe :=
  connect (link obs mem).

Definition well_stamped_label (st : State) (l : Label) :=
  forall f1 f2, f1 \in root_set l st -> reachable l (st_mem st) f1 f2 ->
  isLow (Mem.stamp f2) l.

Definition well_stamped (st : State) :=
  forall l, well_stamped_label st l.

Lemma stamp_alloc μ μ' sz lab stamp i li fp :
  alloc sz lab stamp (Vint i@li) μ = Some (fp, μ') ->
  Mem.stamp fp = stamp.
Proof.
rewrite /alloc /zreplicate.
case: (ZArith_dec.Z_lt_dec sz 0) => // lt0sz [alloc_sz].
by rewrite (Mem.alloc_stamp alloc_sz).
Qed.

Lemma reachable_alloc_int μ μ' sz lab stamp i li fp l f1 f2 :
  alloc sz lab stamp (Vint i@li) μ = Some (fp, μ') ->
  reachable l μ' f1 f2 = reachable l μ f1 f2.
Proof.
rewrite /alloc /zreplicate.
case: (ZArith_dec.Z_lt_dec sz 0) => // lt0sz /= [alloc_sz].
apply/eq_connect=> x y.
rewrite /link.
have [<-|neq_fpx] := fp =P x.
  (* How about using implicit arguments? *)
  rewrite (alloc_get_frame_eq _ _ _ _ _ _ alloc_sz) inE /=.
  rewrite (Mem.alloc_get_fresh alloc_sz).
  set s := filter _ _.
  suff /eqP->: s == [::] by rewrite andbF.
  by rewrite -[_ == _]negbK -has_filter has_nseq andbF.
by rewrite (alloc_get_frame_neq _ _ _ _ _ _ _ alloc_sz neq_fpx).
Qed.

Arguments reachable_alloc_int [μ μ' sz lab stamp i li fp l f1 f2] _.

Lemma reachable_upd μ μ' pv lf fr l f1 f2 :
  Mem.upd_frame μ pv (Fr lf fr) = Some μ' ->
  reachable l μ' f1 f2 -> reachable l μ f1 f2
  \/ isLow lf l /\ reachable l μ f1 pv
    /\ exists f3, f3 \in mframes_from_atoms l fr /\ reachable l μ f3 f2.
Proof.
  (* TODO: use splitPl with pv *)
move=> upd_pv /connectP [p] /(@shortenP _ _ f1) [p'].
have link_not_pv: forall (f : mframe), pv != f -> link l μ' f =1 link l μ f.
  move=> f; rewrite eq_sym => /eqP neq_pv f'; rewrite /link.
  by rewrite (get_frame_upd_frame_neq upd_pv neq_pv).
have path_not_pv: forall (p : seq mframe) f, pv \notin belast f p -> path (link l μ') f p = path (link l μ) f p.
  elim=> //= x s IHs f.
  rewrite inE negb_or.
  case/andP => neq_pv ?.
  by rewrite IHs // link_not_pv.
have [in_path|] := boolP (pv \in f1 :: p').
  case/(@splitPl _ f1 p'): in_path => p1 [|f3 p2 last_p1].
    rewrite cats0 => last_p1 path_p1 uniq_p1 _ ->; left; apply/connectP.
    exists p1 => //; rewrite -path_not_pv //.
    by move: uniq_p1; rewrite lastI last_p1 rcons_uniq => /andP [].
  rewrite cat_path last_p1 -cat_cons [f1 :: p1]lastI last_p1 cat_uniq last_cat.
  rewrite rcons_uniq.
  case/andP=> path_p1 path_p2 /and3P [/andP [? _] not_pv _] _ /= ->; right.
  rewrite /= {1}/link (get_frame_upd_frame_eq upd_pv) in path_p2.
  case/andP: path_p2 => /andP [low_lf ref_f3] path_p2; split=> //; split.
    by apply/connectP; exists p1=> //; rewrite -path_not_pv.
  exists f3; split => //; apply/connectP; exists p2 => //.
  rewrite -path_not_pv //; apply/negP=> pv_in_p2; case/negP: not_pv.
  apply/(@sub_has _ (pred1 pv)).
    by move=> ? /= /eqP ->; rewrite mem_rcons inE eqxx.
  by rewrite has_pred1 lastI mem_rcons inE pv_in_p2 orbT.
rewrite lastI mem_rcons inE negb_or=> /andP [_ ?] path_p' _ _ ->; left.
by apply/connectP; exists p' => //; rewrite -path_not_pv.
Qed.

Lemma well_stamped_preservation st st' : well_stamped st ->
  step default_table st st' -> well_stamped st'.
Proof.
move=> wf_st step.
move: wf_st.
case: {st st'} step.
(* Lab *)
+ move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> ? ? [<- <-] upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* PcLab *)
+ move=> im μ σ pc r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd upd_r1)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* MLab *)
+ move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> ? ? get_r1 [].
  rewrite /Vector.nth_order /= => <- <- upd_r2 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd upd_r2)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* PutLab *)
+ move=> im μ σ pc r r' r1 j LPC rl rpcl l' -> ? [<- <-] upd_r1 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite inE.
  case/orP=> [|in_stack_f1].
    move/(subsetP (root_set_registers_upd upd_r1)).
    rewrite inE.
    case/orP=> [in_regs_f1|].
      by rewrite inE in_regs_f1 in wf_st; apply: wf_st.
    by rewrite inE.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* Call *)
+ move=> im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl -> ? get_r1 get_r2 [<- <-] wf_st l f1 f2.
  rewrite /Vector.nth_order /=.
  move: wf_st => /(_ l f1 f2) /= wf_st.
  rewrite root_set_registers_join !inE; case/orP.
    by case/andP=> _ in_regs_f1; apply: wf_st; rewrite inE in_regs_f1.
  rewrite low_join.
  case: ifPn=> [/andP [_ low_Lpc]|_ in_stack_f1].
    by rewrite /root_set_registers low_Lpc in wf_st *.
  by rewrite inE in_stack_f1 orbT in wf_st; apply: wf_st.
(* BRet *)
+ move=> im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl -> -> ? get_r1.
  rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
  case: ifPn=> // Hjoins [<- <-] upd_r1 wf_st l f1 f2 /=.
  move: wf_st => /(_ l f1 f2) /=.
  rewrite !inE => wf_st.
  case/orP=> [|in_stack_f1].
    rewrite /root_set_registers; case: ifP => low_LPC'; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_r1)).
    rewrite inE; case/orP=> [in_r'_f1|].
      by rewrite low_LPC' inE in_r'_f1 orbT in wf_st; apply: wf_st.
    case: a get_r1 upd_r1 => [?|[fp i]|?] get_r1 upd_r1; rewrite /mframes_from_atoms /= !inE //.
    case: ifP=> // low_B.
    rewrite /= inE => /eqP eq_f1.
    move: wf_st.
    rewrite eq_f1 (root_set_registers_nth get_r1); first exact.
      exact/(join_2_rev R)/(flows_trans _ _ _ Hjoins)/join_minimal.
    exact/(join_1_rev R LPC)/(flows_trans _ _ _ Hjoins)/join_minimal.
  by case: (isLow LPC' l) wf_st; rewrite ?inE in_stack_f1 !orbT; apply.
(* Alloc *)
+ move=> im μ μ' σ pc r r' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp -> ? get_r1 get_r2 [<- <-] alloc_i.
  move: (alloc_i); rewrite /alloc.
  case: (zreplicate i (Vint 0 @ ⊥)) => // ? [malloc].
  rewrite /Vector.nth_order /= => upd_r3 wf_st l f1 f2.
  move: wf_st => /(_ l f1 f2) /=.
  rewrite (reachable_alloc_int alloc_i) !inE => wf_st.
  case/orP=> [|in_stack_f1].
    rewrite /root_set_registers.
    case: ifP => low_LPC; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_r3)).
    rewrite inE.
    case/orP=> [in_r_f1|].
      by move: wf_st; rewrite /root_set_registers low_LPC in_r_f1; apply.
    rewrite /mframes_from_atoms /=.
    case low_KK': (isLow (K \_/ K') l); last by rewrite inE.
    rewrite /= !inE => /eqP ->.
    case/connectP=> [[_ ->|]] /=.
      by rewrite (stamp_alloc alloc_i) /= joinA low_join low_KK' low_LPC.
    move=> a s.
    by rewrite /link /= (Mem.alloc_get_fresh malloc).
  by move: wf_st; rewrite in_stack_f1 orbT; apply.
(* Load *)
+ move=> im μ σ pc C [pv pl] K r r' r1 r2 j LPC v Ll rl rpcl -> ? get_r1 load_p mlab_p [<- <-].
  rewrite /Vector.nth_order /= => upd_r2 wf_st l f1 f2 /=.
  rewrite inE; case/orP=> [|in_stack_f1].
    rewrite /root_set_registers.
    case: ifP; last by rewrite inE.
    rewrite !low_join; case/and3P=> low_LPC low_K low_C.
    move/(subsetP (mframes_from_atoms_upd upd_r2)).
    rewrite inE; case/orP=> [in_r_f1|].
      by apply: wf_st; rewrite inE /root_set_registers low_LPC in_r_f1.
    rewrite inE /=; case: v load_p upd_r2 => // [[fp ?]] load_p upd_r2.
    case low_Ll: (isLow Ll l) => //=.
    rewrite !inE.
    move/eqP=> -> reach_f2.
    apply: (wf_st l pv f2); first by rewrite inE (root_set_registers_nth get_r1).
    apply/(connect_trans _ reach_f2)/connect1; move: load_p mlab_p.
    rewrite /link /=; case: (Mem.get_frame μ pv) => // [[? fr]] get_pl [->].
    apply/andP; split=> //.
    exact: (mframes_from_atoms_nth get_pl).
  by apply: wf_st; rewrite inE in_stack_f1 orbT.
(* Store *)
+ move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl lp lf lv -> ? get_r1 get_r2 /= lab_p.
  rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
  case: ifP => //; rewrite flows_join; case/andP => low_lp_lf low_LPC_lf [<- <-].
  case get_fp: (Mem.get_frame μ fp) lab_p => // [[? fr]] [eq_lf].
  rewrite eq_lf in get_fp *.
  case upd_i: (update_list_Z fr i (v @ lv)) => [fr'|] // upd_fp wf_st l f1 f2.
  rewrite inE /= => H.
  case/(reachable_upd upd_fp) => [|[low_lf [reach_fp [f3 []]]]].
    by apply: wf_st; rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_i)); rewrite inE.
    case/orP=> [in_fr_f3 reach_f2|].
      apply: (wf_st l f1 f2) => /=; first by rewrite inE.
      apply/(connect_trans reach_fp)/(connect_trans _ reach_f2)/connect1.
      by rewrite /link get_fp low_lf.
    case: v get_r2 upd_i => [|[pv pi] get_r2 upd_i|]; rewrite /mframes_from_atoms /= ?inE //.
    case: ifP => // low_lv; rewrite inE => /eqP ->; apply: wf_st.
    rewrite inE /= /root_set_registers (root_set_registers_nth get_r2) //.
    exact/(flows_trans _ _ _ low_LPC_lf).
(* Write *)
+ move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl v' lp lv lv' lf -> ? get_r1 get_r2 /= load_fp lab_fp.
  rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
  case: ifP => //; rewrite !flows_join=> /andP [/andP [low_LPC low_lp] low_lv] [<- <-].
  case get_fp: (Mem.get_frame μ fp) lab_fp => // [[? fr]] [eq_lf].
  rewrite eq_lf in get_fp *.
  case upd_i: (update_list_Z fr i (v @ lv')) => [fr'|] // upd_fp wf_st l f1 f2.
  rewrite inE /= => H.
  case/(reachable_upd upd_fp) => [|[low_lf [reach_fp [f3 []]]]].
    by apply: wf_st; rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_i)); rewrite inE.
    case/orP=> [in_fr_f3 reach_f2|].
      apply: (wf_st l f1 f2) => /=; first by rewrite inE.
      apply/(connect_trans reach_fp)/(connect_trans _ reach_f2)/connect1.
      by rewrite /link get_fp low_lf.
    case: v get_r2 upd_i => [|[pv pi] get_r2 upd_i|]; rewrite /mframes_from_atoms /= ?inE //.
    case: ifP => // low_lv'; rewrite inE => /eqP ->; apply: wf_st.
    rewrite inE /= /root_set_registers (root_set_registers_nth get_r2) //.
      by apply/(flows_trans _ _ _ low_LPC); rewrite flows_join low_lv' low_lf.
by apply/(flows_trans _ _ _ low_lv); rewrite flows_join low_lv' low_lf.
(* Jump *)
+ move=> im μ σ pc addr Ll r r1 j LPC rpcl -> ? get_r1 [<-] wf_st l f1 f2.
  rewrite /Vector.nth_order /= root_set_registers_join !inE.
  case/orP=> [/andP [in_regs_f1 _]|in_stack_f1]; apply: wf_st; rewrite inE.
    by rewrite in_regs_f1.
  by rewrite in_stack_f1 orbT.
(* BNZ *)
+ move=> im μ σ pc n m K r r1 j LPC rpcl -> ? get_r1 [<-] wf_st l f1 f2.
  rewrite /Vector.nth_order /= root_set_registers_join !inE.
  case/orP=> [/andP [_ in_regs_f1]|in_stack_f1]; apply: wf_st; rewrite inE.
    by rewrite in_regs_f1.
  by rewrite in_stack_f1 orbT.
(* PSetOff *)
  + move=> im μ σ pc fp' j K1 n K2 r r' r1 r2 r3 j' LPC rl rpcl -> ? get_r1 get_r2 [<- <-].
  rewrite /Vector.nth_order /= => upd_r3 wf_st l f1 f2.
  rewrite inE; case/orP=> [|in_stack_f1] /=.
    rewrite /root_set_registers; case: ifP => // low_LPC; last by rewrite inE.
    move/(subsetP (mframes_from_atoms_upd upd_r3)).
    rewrite inE; case/orP=> [in_regs_f1|] /=.
      by apply: wf_st; rewrite inE /root_set_registers low_LPC in_regs_f1.
    rewrite inE /= low_join.
    case: ifP => //= /andP [? ?].
    rewrite inE => /eqP ->.
    apply: wf_st.
    rewrite inE.
    rewrite (root_set_registers_nth get_r1) //.
  by apply: wf_st; rewrite inE in_stack_f1 orbT.
(* Put *)
  + move=> im μ σ pc x r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 wf_st l f1 f2.
    rewrite inE; case/orP=> [|in_stack_f1] /=.
      move/(subsetP (root_set_registers_upd upd_r1)).
      rewrite inE; case/orP=> [in_regs_f1|].
        by apply: wf_st; rewrite inE in_regs_f1.
      by rewrite !inE.
    by apply: wf_st; rewrite inE in_stack_f1 orbT.
(* BinOp *)
  + move=> im μ σ pc o v1 L1 v2 L2 v r r1 r2 r3 r' j LPC rl rpcl -> _ get_r1 get_r2 [<- <-] eval.
    rewrite /Vector.nth_order /= => upd_r3 wf_st l f1 f2.
    rewrite inE; case/orP=> [|in_stack_f1].
      move/(subsetP (root_set_registers_upd upd_r3)).
      rewrite inE; case/orP=> [in_regs_f1|] /=.
        by apply: wf_st; rewrite inE in_regs_f1.
      by case: o eval; case: v1 get_r1 => ? ; case: v2 get_r2 => ? //= _ _ [<-]; rewrite !inE.
    by apply: wf_st; rewrite inE in_stack_f1 orbT.
(* Nop *)
  + move=> im μ σ pc r j LPC rpcl -> _ [<-] wf_st l f1 f2.
    exact: wf_st.
(* MSize *)
  + move=> im μ σ pc p K C r r' r1 r2 j LPC rl rpcl n -> _ get_r1 lab_p [<- <-] size_p.
    rewrite /Vector.nth_order /= => upd_r2 wf_st l f1 f2.
    rewrite inE; case/orP=> [|in_stack_f1].
      rewrite root_set_registers_join inE; case/andP=> in_regs_f1 _.
      move/(subsetP (root_set_registers_upd upd_r2)): in_regs_f1.
      rewrite inE; case/orP=> [in_regs_f1|] /=.
        by apply: wf_st; rewrite inE in_regs_f1.
      by rewrite inE.
    by apply: wf_st; rewrite inE in_stack_f1 orbT.
(* PGetOff *)
  + move=> im μ σ pc fp' j K r r' r1 r2 j' LPC rl rpcl -> _ get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 wf_st l f1 f2.
    rewrite inE; case/orP=> [|in_stack_f1].
      move/(subsetP (root_set_registers_upd upd_r2)).
      rewrite inE; case/orP=> [in_regs_f1|] /=.
        by apply: wf_st; rewrite inE in_regs_f1.
      by rewrite inE.
    by apply: wf_st; rewrite inE in_stack_f1 orbT.

(* Mov *)
  + move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> _ get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 wf_st l f1 f2.
    rewrite inE; case/orP=> [|in_stack_f1].
    rewrite /root_set_registers; case: ifP => low_LPC; last by rewrite inE.
      move/(subsetP (mframes_from_atoms_upd upd_r2)).
      rewrite inE; case/orP=> [in_regs_f1|] /=.
        by apply: wf_st; rewrite inE /root_set_registers low_LPC in_regs_f1.
      case: v get_r1 upd_r2 => [|[? ?]|] get_r1 upd_r2; try by rewrite inE.
      rewrite inE /=; case: ifP => // low_K /=; rewrite inE=> /eqP ->.
      apply: wf_st; rewrite inE /root_set_registers low_LPC.
      by rewrite (mframes_from_atoms_nth get_r1).
    by apply: wf_st; rewrite inE in_stack_f1 orbT.
Qed.

Lemma indist_low_pc obs st1 st2 :
  isLow ∂(st_pc st1) obs ->
  indist obs st1 st2 =
  [&& indist obs (st_imem st1) (st_imem st2),
   indist obs (st_mem st1) (st_mem st2),
   indist obs (st_stack st1) (st_stack st2),
   st_pc st1 == st_pc st2 &
   indist obs (st_regs st1) (st_regs st2)].
Proof.
  case: st1 => im1 mem1 stk1 regs1 pc1; case: st2 => im2 mem2 stk2 regs2 pc2.
  rewrite /GenericIndist.indist /=.
  by move => -> /=; do 3!bool_congr.
Qed.

Lemma indist_instr obs st1 st2 :
  indist obs st1 st2 ->
  isLow ∂(st_pc st1) obs ->
  state_instr_lookup st1 = state_instr_lookup st2.
Proof.
  move => Hindist Hlow.
  rewrite (indist_low_pc _ Hlow) in Hindist.
  rewrite /state_instr_lookup.
  by case/and5P: Hindist => /eqP -> _ _ /eqP -> _.
Qed.

Lemma indist_registerContent_aux obs rs1 rs2 r :
  indist obs rs1 rs2 ->
  indist obs (registerContent rs1 r) (registerContent rs2 r).
Proof.
  rewrite /registerContent.
  rewrite /indist /indistList /nth_error_Z.
  case: (BinInt.Z.ltb r 0) => //=.
  elim: {r} (BinInt.Z.to_nat r) rs1 rs2
        => [|n IH] [|x xs] [|y ys] //=.
  - by case/and3P.
  - move/(_ xs ys) in IH; rewrite eqSS; case/and3P=> Hs _ H.
    by apply: IH; rewrite Hs H.
Qed.

Lemma indist_registerContent obs st1 st2 r v1 :
  indist obs st1 st2 ->
  isLow ∂(st_pc st1) obs ->
  registerContent (st_regs st1) r = Some v1 ->
  exists2 v2,
    registerContent (st_regs st2) r = Some v2 &
    indist obs v1 v2.
Proof.
  move => Hindist Hlow.
  rewrite (indist_low_pc _ Hlow) in Hindist.
  case/and5P: Hindist => _ _ _ _.
  move => Hindist Hdef.
  move: (indist_registerContent_aux r Hindist).
  rewrite Hdef.
  case: (registerContent (st_regs st2) r) => [v2|] //=.
  by eauto.
Qed.

Lemma indist_registerUpdate_aux obs rs1 rs2 r v1 v2 :
  indist obs rs1 rs2 ->
  indist obs v1 v2 ->
  indist obs (registerUpdate rs1 r v1) (registerUpdate rs2 r v2).
Proof.
  rewrite /registerUpdate /update_list_Z.
  case: (BinInt.Z.ltb r 0) => //=.
  elim: {r} (BinInt.Z.to_nat r) rs1 rs2
        => [|n IH] [|x xs] [|y ys] //=.
  - rewrite /indist /= /indist /indistList //= /indist.
    by rewrite eqSS; move => /and3P [-> _ ->] /= ->.
  - rewrite /indist /= /indist /indistList /= eqSS.
    move/and3P => [Hs Hxy Hxsys] Hv1v2.
    move: IH Hxy => /(_ xs ys); rewrite Hs Hxsys => /(_ erefl Hv1v2) {Hxsys Hv1v2}.
    case: (update_list xs n v1) => [xs'|]; case: (update_list ys n v2) => [ys'|] //=.
    rewrite /indist /= /indistList /indist eqSS.
    by case/andP=> [-> ->] /= ->.
Qed.

Lemma indist_registerUpdate obs st1 st2 r v1 v2 regs1 :
  indist obs st1 st2 ->
  isLow ∂(st_pc st1) obs ->
  indist obs v1 v2 ->
  registerUpdate (st_regs st1) r v1 = Some regs1 ->
  exists2 regs2,
    registerUpdate (st_regs st2) r v2 = Some regs2 &
    indist obs regs1 regs2.
Proof.
  move => Hindist Hlow.
  move: Hindist.
  rewrite indist_low_pc // => /and5P [_ _ _ _ Hindist] Hv1v2 Hupd.
  move: (indist_registerUpdate_aux r Hindist Hv1v2).
  rewrite Hupd.
  case: (registerUpdate (st_regs st2) r v2) => [regs2|] //=.
  by eauto.
Qed.

Lemma indist_pc obs st1 st2 :
  indist obs st1 st2 ->
  isLow ∂(st_pc st1) obs ->
  st_pc st1 = st_pc st2.
Proof.
by move=> i l; case/and3P: i=> [_ _]; rewrite l /= => /and3P [/eqP ->].
Qed.

Lemma pc_eqS pc pc' l1 l2 :
  (PAtm (BinInt.Z.add pc 1) l1 == PAtm (BinInt.Z.add pc' 1) l2) =
  (PAtm pc l1 == PAtm pc' l2).
Proof.
by apply/eqP/eqP=> [[? ->]|[-> ->] //]; congr PAtm; omega.
Qed.

Lemma indist_pcl obs st1 st2 :
  indist obs st1 st2 ->
  isLow ∂(st_pc st1) obs = isLow ∂(st_pc st2) obs.
Proof.
case/and3P=> [_ _].
have [low1|high1] := boolP (isLow _ _)=> /=.
  by case/and4P=> [/eqP <-]; rewrite low1.
have [low2|high2] := boolP (isLow _ _)=> //=.
by case/and4P=> [/eqP e _ _ _]; move: high1; rewrite e low2.
Qed.

Lemma high_low obs s s' :
  fstep default_table s = Some s' ->
  isHigh ∂(st_pc s)  obs ->
  isLow  ∂(st_pc s') obs ->
  state_instr_lookup s = Some BRet.
Proof.
case/fstepP.
(* Lab *)
- by move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> /= instr get_r1 [<- <-] upd_r2 /negbTE ->.
(* PcLab *)
- by move=> im μ σ pc r r' r1 j LPC rl rpcl -> /= CODE [<- <-] upd_r1 /negbTE ->.
(* MLab *)
- by move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> ? ? get_r1 [] /= _ <- _ /negbTE ->.
(* PutLab *)
- by move=> im μ σ pc r r' r1 j LPC rl rpcl l' -> ? [<- <-] upd_r1 /= /negbTE ->.
(* Call *)
- move=> im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl -> ? get_r1 get_r2 [<- <-].
  by rewrite /= flows_join andbC => /negbTE ->.
(* BRet *)
- move=> im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl -> -> /= CODE get_r1.
  by rewrite /state_instr_lookup /=.
(* Alloc *)
- by move=> im μ μ' σ pc r r' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp -> ? _ _ [<- <-] _ _ /= /negbTE ->.
(* Load *)
- move=> im μ σ pc C [pv pl] K r r' r1 r2 j LPC v Ll rl rpcl -> ? get_r1 load_p mlab_p [<- <-].
  rewrite /Vector.nth_order /= => upd_r2.
  by rewrite !flows_join => /negbTE ->.
(* Store *)
- move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl lp lf lv -> ? get_r1 get_r2 /= lab_p.
  rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
  case: ifP => //; rewrite flows_join; case/andP => low_lp_lf low_LPC_lf [<- <-].
  by move=> _ /negbTE ->.
(* Write *)
- move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl v' lp lv lv' lf -> ? get_r1 get_r2 /= load_fp lab_fp.
  rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
  case: ifP => //; rewrite !flows_join=> /andP [/andP [low_LPC low_lp] low_lv] [<- <-].
  by move=> _ /negbTE ->.
(* Jump *)
- move=> im μ σ pc addr Ll r r1 j LPC rpcl -> ? get_r1 [<-] /=.
  by rewrite flows_join => /negbTE ->.
(* BNZ *)
- move=> im μ σ pc n m K r r1 j LPC rpcl -> ? get_r1 [<-] /=.
  by rewrite flows_join andbC => /negbTE ->.
(* PSetOff *)
- move=> im μ σ pc fp' j K1 n K2 r r' r1 r2 r3 j' LPC rl rpcl -> ? get_r1 get_r2 [<- <-] /=.
  by move=> _ /negbTE ->.
(* Put *)
- by move=> im μ σ pc x r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 /= /negbTE ->.
(* BinOp *)
- move=> im μ σ pc op v1 L1 v2 L2 v r r1 r2 r3 r' j LPC rl rpcl -> _ get_r1 get_r2 [<- <-] eval.
  by move=> _ /= /negbTE ->.
(* Nop *)
- by move=> im μ σ pc r j LPC rpcl -> _ [<-] /= /negbTE ->.
(* MSize *)
- move=> im μ σ pc p K C r r' r1 r2 j LPC rl rpcl n -> _ get_r1 lab_p [<- <-] size_p _ /=.
  by rewrite flows_join => /negbTE ->.
(* PGetOff *)
- by move=> im μ σ pc fp' j K r r' r1 r2 j' LPC rl rpcl -> _ get_r1 [<- <-] /= _ /negbTE ->.
(* Mov *)
- by move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> _ get_r1 [<- <-] /= _ /negbTE ->.
Qed.

Arguments indist : simpl never.

Theorem SSNI : ssni well_stamped (fstep default_table) (fun obs st => isLow ∂(st_pc st) obs) (indist).
Proof.
constructor=> [obs s1 s2 s1' s2' wf_s1 wf_s2 low_pc indist_s1s2 /fstepP step1|o s1 s1' wf_s1 /= high_pc1 high_pc2 /fstepP step1|o s1 s2 s1' s2' wf_s1 wf_s2 /= high_pc1 indist_s1s2 low_pc1' low_pc2' /fstepP step1].
- case: step1 low_pc indist_s1s2 wf_s1.
  (* Lab *)
  + move=> im μ σ v K pc regs1 regs1' r1 r2 j LPC rl rpcl -> instr get_r1 [<- <-] upd_r2 low_pc indist_s1s2 wf_s1.
    rewrite /= in instr.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= instr /=.
    case: s2 wf_s2 indist_s1s2 => im2 μ2 σ2 regs2 [pcv2 pcl2] wf_s2 indist_s1s2.
    have /= [[v2 lv2] -> /andP [/eqP <-]] :=
      indist_registerContent indist_s1s2 low_pc get_r1.
    have /= [regs2' -> indist_regs _ [<-]] :=
      indist_registerUpdate indist_s1s2 low_pc (indistxx (Vlab K @ ⊥)) upd_r2.
    rewrite /indist /=; case/and3P: indist_s1s2.
    by rewrite indist_regs low_pc pc_eqS !andbT => /= -> -> /= /and3P [-> -> _].
  (* PcLab *)
  + move=> im μ σ pc r r' r1 j LPC rl rpcl -> /= CODE [<- <-] upd_r1 low_pc indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => im2 μ2 σ2 regs2 [pcv2 pcl2] wf_s2 indist_s1s2.
    have /= [_ eq_pc] := indist_pc indist_s1s2 low_pc.
    rewrite -eq_pc in indist_s1s2 *.
    have /= [? -> indist_r' [<-]] :=
      indist_registerUpdate indist_s1s2 low_pc (indistxx (Vlab LPC @ ⊥)) upd_r1.
    rewrite /indist /=; case/and3P: indist_s1s2.
    by rewrite indist_r' low_pc pc_eqS !andbT => /= -> -> /= /and3P [-> -> _].
  (* MLab *)
  + move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> /= CODE mlab_p get_r1 [].
    rewrite /Vector.nth_order /= => <- <- upd_r2 low_pc indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => im2 μ2 σ2 regs2 [pcv2 pcl2] wf_s2 indist_s1s2.
    have /= [[[] // p2 lv2] -> // /andP [/eqP <- indist_ptr] {lv2}] :=
      indist_registerContent indist_s1s2 low_pc get_r1.
    case mlab_p2: mlab => [C2|] //=; rewrite /Vector.nth_order /=.
    have indist_v: indist obs (Vlab C @ K) (Vlab C2 @ K).
      rewrite /indist /= eqxx /= /indist /indistValue /eq_op /=.
      move: indist_ptr mlab_p2; have [K_low|//] //= := boolP (flows K obs).
      move=> /eqP [<-] {p2}.
      case/and3P: indist_s1s2=> /= [_ /andP [/allP im1m2 _] _] mlab_p2.
      case: p mlab_p mlab_p2 get_r1 => [b off] /=.
      case get_b: (Mem.get_frame μ b) => [[C' vs]|] //= [e]; subst C'.
      case get_b2: (Mem.get_frame μ2 b) => [[C2' vs2]|] //= [e] get_r1; subst C2'.
      have b_low: flows (Mem.stamp b) obs.
        apply: (wf_s1 obs b b).
          apply/setUP; left.
          by apply/(root_set_registers_nth get_r1).
        by rewrite /reachable /= connect0.
      have /(im1m2 _) {im1m2}: b \in blocks_stamped_below obs μ.
        apply/Mem.get_blocks_spec.
        by rewrite get_b andbT /allThingsBelow mem_filter all_elems andbT.
      by rewrite get_b get_b2 /indist /= /indist /= => /andP [].
    have /= [? -> indist_r' [<-]] := indist_registerUpdate indist_s1s2 low_pc indist_v upd_r2.
    rewrite /indist /=; case/and3P: indist_s1s2.
    by rewrite indist_r' low_pc pc_eqS !andbT => /= -> -> /= /and3P [-> -> _].
  (* PutLab *)
  + move=> im μ σ pc r r' r1 j LPC rl rpcl l' -> /= CODE [<- <-] upd_r1 low_pc indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => im2 μ2 σ2 regs2 [pcv2 pcl2] wf_s2 indist_s1s2.
    have indist_v: indist obs (Vlab l' @ ⊥) (Vlab l' @ ⊥).
      by rewrite /indist /= eqxx /indist /indistValue eqxx orbT.
    have /= [? -> indist_r' [<-]] := indist_registerUpdate indist_s1s2 low_pc indist_v upd_r1.
    rewrite /indist /=; case/and3P: indist_s1s2.
    by rewrite indist_r' low_pc pc_eqS !andbT => /= -> -> /= /and3P [-> -> _].
   (* Call *)
  + move=> im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl -> /= CODE get_r1 get_r2 [<- <-] low_pc indist_s1s2 wf_s1.
    rewrite /Vector.nth_order /=.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => im2 μ2 σ2 regs2 [pcv2 pcl2] wf_s2 indist_s1s2.
    have /= [[[] // ? ? -> // /andP [/eqP <- indist_addr]]] :=
      indist_registerContent indist_s1s2 low_pc get_r1.
    have /= [[] // [] // ? ? -> // /andP [/eqP <- indist_B] [<-]] :=
      indist_registerContent indist_s1s2 low_pc get_r2.
    rewrite /Vector.nth_order /=.
    rewrite /indist /=; case/and3P: indist_s1s2.
    rewrite low_pc => -> -> /= /and3P [/eqP [<- <-] indist_stack indist_r].
    rewrite orbb low_join low_pc andbT.
    case: ifP indist_addr => /= [low_La /eqP [<-]|hi_La _].
      rewrite eqxx /= indist_r andbT /indist /= /indist /= eqSS.
      case/andP: indist_stack => [-> ->]; rewrite andbT /=.
      rewrite /indist /= orbb flows_join low_pc andbT !eqxx indist_r /=.
      by rewrite implybE.
    rewrite /cropTop /= flows_join low_pc andbT.
    case: (boolP (isLow K obs)) indist_B=> [low_K|hi_K _] /=.
      move/eqP=> [<-]; rewrite indist_cons; apply/andP; split=> //.
      by rewrite /indist /= orbb indist_r !eqxx /= implybT.
    case: (σ) (σ2) indist_stack => [s] [s2]; rewrite {1}/indist /=.
    elim: s s2=> [|[[rpc1 rpcl1] rs1 rr1 rl1] st1 IH] [|[[rpc2 rpcl2] rs2 rr2 rl2] st2] //=.
    rewrite indist_cons {1}/indist /= implybE negb_or.
    case/andP=> [/orP [/andP [H1 H2]|E] Hindist]; move/(_ _ Hindist) in IH.
      by rewrite (negbTE H1) (negbTE H2); eauto.
    case/and4P: E => [/eqP [-> ->] Hrs /eqP -> /eqP ->].
    case: ifP=> //= low2; rewrite indist_cons Hindist andbT.
    by rewrite /indist /= low2 !eqxx Hrs.
  (* BRet *)
  + move=> im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl -> -> /= CODE get_r1.
    rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
    case: ifPn=> // Hjoins [<- <-] upd_r1 low_pc indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => [im2 μ2 [[|sf σ2]] r2 [j2 LPC2]] //=.
    case: sf=> [[j2' LPC2'] r2' r12 B2] wf_s2 indist_s1s2.
    move: indist_s1s2 (indist_s1s2) wf_s2.
    rewrite {1}indist_low_pc //= {3}/indist /=.
    case/and5P => [indist_im indist_μ indist_s /eqP [<- <-] {j2 LPC2} indist_r].
    move: indist_s; rewrite indist_cons {1}/indist /= => /andP [indist_sf indist_s].
    case get_r12: (registerContent r2 r12) => [[a2 R2]|] //= indist_s1s2 wf_s2.
    rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
    case: ifPn=> // Hjoins2.
    case upd_r12: (registerUpdate _ _ _)=> [r2''|] //= [<-].
    rewrite /indist /= indist_im indist_μ /=.
    move: indist_sf; case: ifPn=> /=.
      move=> low_pc' ind; move: low_pc' indist_s1s2 get_r12 wf_s2 upd_r12 Hjoins2.
      case/and4P: ind=> [/eqP [<- <-] indist_r' /eqP <- /eqP <-] {j2' LPC2' r12 B2}.
      rewrite orbb=> low_pc' indist_s1s2 get_r12.
      move: (indist_registerContent_aux r1 indist_r)=> /=.
      rewrite get_r1 get_r12 eqxx /= => /andP [/eqP eR indist_a].
      rewrite -{}eR {R2} in get_r12 *; rewrite {1}/indist /= indist_s /=.
      move=> wf_s2 upd_r12 _.
      have [low|hi] := boolP (isLow B obs).
        move: Hjoins indist_a; rewrite flows_join => /andP [lowR _].
        rewrite (flows_trans _ _ _ lowR) /= => [indist_a|].
          have {indist_a} indist_a : indist obs (a @ B) (a2 @ B).
            by rewrite /indist /= eqxx low.
          move: (indist_registerUpdate_aux r1 indist_r' indist_a).
          by rewrite upd_r1 upd_r12.
        by rewrite flows_join low.
      have {indist_a} indist_a : indist obs (a @ B) (a2 @ B).
        by rewrite /indist /= eqxx hi.
      move: (indist_registerUpdate_aux r1 indist_r' indist_a).
      by rewrite upd_r1 upd_r12.
    move=> _ _.
    elim: σ σ2 indist_s {indist_s1s2 wf_s1 wf_s2}=> [|sf σ IH] [|sf2 σ2] //=.
    case: sf sf2=> {j' j2' LPC' LPC2' Hjoins Hjoins2 r' r2' upd_r1 upd_r12 r1 r12 get_r1 get_r12}
                   [[j' LPC'] r' r1 L] [[j2' LPC2'] r2' r12 L2].
    rewrite !cropTop_cons indist_cons {1}/indist /=.
    have [low /= /andP [Hind Hind_s]|/norP [/negbTE -> /negbTE ->] Hind_s] := boolP (isLow _ _ || isLow _ _).
      case/and4P: Hind low=> [/eqP [<- <-] hr hr1 hL] {LPC2'}.
      rewrite orbb => low; rewrite low /= indist_cons {1}/indist /= low /= Hind_s andbT.
      by apply/and4P; split.
    by auto.
  (* Alloc *)
  + move=> im μ μ' σ pc rs rs' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp -> /= CODE
           get_r1 get_r2 [<- <-] alloc_i.
    move: alloc_i get_r1; rewrite /alloc /zreplicate.
    case: (ZArith_dec.Z_lt_dec i 0) => [//|Pi] /=.
    have {Pi} Pi: BinInt.Z.le 0 i by omega.
    rewrite -{2}(Znat.Z2Nat.id _ Pi) {Pi}.
    move: (BinInt.Z.to_nat i) => {i} i [Halloc] get_r1.
    rewrite /Vector.nth_order /= => upd_r3 low_pc indist_s1s2 wf_s1.
    move: (indist_s1s2); rewrite (indist_low_pc) //= => indist_s1s2'.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 indist_s1s2'
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2 indist_s1s2'.
    have /= [[[] // i2 K2 -> // /andP [/eqP <- indist_i]]] :=
      indist_registerContent indist_s1s2 low_pc get_r1.
    have /= [[[] // Ll2 K2' -> // /andP [/eqP <- indist_Ll]]] :=
      indist_registerContent indist_s1s2 low_pc get_r2.
    move=> alloc_i2; move: alloc_i2 indist_i.
    rewrite /alloc /zreplicate.
    case: ZArith_dec.Z_lt_dec=> [//|Pi2] /=.
    have {Pi2} Pi2: BinInt.Z.le 0 i2 by omega.
    rewrite -{2}(Znat.Z2Nat.id _ Pi2) {Pi2}.
    move: (BinInt.Z.to_nat i2) => {i2} i2.
    case Halloc2: Mem.alloc=> [dfp2 μ2'].
    rewrite /Vector.nth_order /=.
    case upd_r32: registerUpdate => [rs2'|] //= [<-] {s2'} indist_i.
    case/and5P: indist_s1s2' indist_s1s2 wf_s2 Halloc2
                => [indist_im indist_μ indist_σ /eqP [<- <-] {j2 LPC2} indist_rs]
                   indist_s1s2 wf_s2 Halloc2.
    rewrite /indist /= low_pc indist_im /= eqxx indist_σ /=.
    have P1: forall μ1 μ2 μ1' μ2' L1 L2 dfp1 dfp2 fr1 fr2,
               indistMemAsym obs μ1 μ2 ->
               isHigh L1 obs -> isHigh L2 obs ->
               Mem.alloc Local μ1 L1 fr1 = (dfp1,μ1') ->
               Mem.alloc Local μ2 L2 fr2 = (dfp2,μ2') ->
               indistMemAsym obs μ1' μ2'.
      move=> {μ μ' μ2 μ2' dfp dfp2 Halloc Halloc2 wf_s1 wf_s2 indist_μ indist_s1s2 upd_r3 upd_r32}.
      move=> μ1 μ2 μ1' μ2' L1 L2 dfp1 dfp2 fr1 fr2 /allP ind hi1 hi2 H1 H2.
      apply/allP=> b.
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter all_elems.
      rewrite andbT (Mem.alloc_get_frame H1) => /andP [low_b].
      rewrite (Mem.alloc_get_frame H2).
      move: low_b; have [<-{b}|] := altP (dfp1 =P b).
        by rewrite (Mem.alloc_stamp H1) (negbTE hi1).
      have [<-{b}|ne1 ne2 low_b get_b] := altP (dfp2 =P b).
        by rewrite (Mem.alloc_stamp H2) (negbTE hi2).
      apply: ind.
      rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec.
      by rewrite mem_filter all_elems low_b.
    case: (boolP (isLow K obs)) indist_i => [low_K /= /eqP Hi|hi_K _] /=.
      move: Hi Halloc2=> [/Znat.Nat2Z.inj <- {i2}] Halloc2.
      case: (boolP (isLow K' obs)) indist_Ll => [low_K' /= /eqP [Hl]|hi_K' _].
        rewrite -{}Hl {Ll2} in Halloc2.
        have e: dfp = dfp2.
          rewrite -[dfp]/(dfp, μ').1 -[dfp2]/(dfp2,μ2').1 -Halloc -Halloc2.
          apply: Mem.alloc_local => b Hb.
          apply/(sameP idP)/(iffP idP).
            case get_b: Mem.get_frame=> [fr|] //= _.
            case/andP: indist_μ=> [_ /allP indist_μ].
            have /(indist_μ b) : b \in blocks_stamped_below obs μ2.
              rewrite /blocks_stamped_below -Mem.get_blocks_spec get_b.
              rewrite /allThingsBelow mem_filter all_elems Hb.
              by rewrite !flows_join low_K low_K' low_pc.
            by rewrite get_b; case: Mem.get_frame.
          case get_b: Mem.get_frame=> [fr|] //= _.
          case/andP: indist_μ=> [/allP indist_μ _].
          have /(indist_μ b) : b \in blocks_stamped_below obs μ.
            rewrite /blocks_stamped_below -Mem.get_blocks_spec get_b.
            rewrite /allThingsBelow mem_filter all_elems Hb.
            by rewrite !flows_join low_K low_K' low_pc.
          by rewrite get_b; case: Mem.get_frame.
        subst dfp2.
        have ind: indist obs (Vptr (Ptr dfp 0) @ K \_/ K') (Vptr (Ptr dfp 0) @ K \_/ K').
          exact: indistxx.
        move: (indist_registerUpdate_aux r3 indist_rs ind).
        rewrite upd_r3 upd_r32 {1}/indist /= => ->; rewrite andbT.
        have P: forall μ1 μ2 μ1' μ2' L dfp fr,
                  indistMemAsym obs μ1 μ2 ->
                  Mem.alloc Local μ1 L fr = (dfp,μ1') ->
                  Mem.alloc Local μ2 L fr = (dfp,μ2') ->
                  indistMemAsym obs μ1' μ2'.
          move=> {μ μ' μ2 μ2' dfp Halloc Halloc2 wf_s1 wf_s2 indist_μ indist_s1s2 upd_r3 upd_r32 ind}.
          move=> μ1 μ2 μ1' μ2' L dfp fr /allP ind H1 H2.
          apply/allP=> b.
          rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter all_elems.
          rewrite andbT (Mem.alloc_get_frame H1) => /andP [low_b].
          rewrite (Mem.alloc_get_frame H2).
          move: low_b; have [<-{b}|ne low_b get_b] := altP (dfp =P b); first by rewrite indistxx.
          suff /(ind b): b \in blocks_stamped_below obs μ1 by [].
          rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec.
          by rewrite mem_filter low_b all_elems.
        case/andP: indist_μ=> [ind1 ind2].
        rewrite /indist /=.
        by rewrite (P _ _ _ _ _ _ _ ind1 Halloc Halloc2) (P _ _ _ _ _ _ _ ind2 Halloc2 Halloc).
      apply/andP; split; last first.
        have indist_dfp: indist obs (Vptr (Ptr dfp 0) @ K \_/ K')
                                    (Vptr (Ptr dfp2 0) @ K \_/ K').
          by rewrite /indist /= eqxx /= flows_join (negbTE hi_K') andbF.
        move: (indist_registerUpdate_aux r3 indist_rs indist_dfp).
        by rewrite upd_r3 upd_r32.
      have hiL: isHigh (K \_/ (K' \_/ LPC)) obs.
        by rewrite !flows_join (negbTE hi_K') andbF.
      case/andP: indist_μ => [ind1 ind2].
      rewrite /indist /= (P1 _ _ _ _ _ _ _ _ _ _ ind1 hiL hiL Halloc Halloc2).
      by rewrite (P1 _ _ _ _ _ _ _ _ _ _ ind2 hiL hiL Halloc2 Halloc).
    have hiL: isHigh (K \_/ (K' \_/ LPC)) obs.
      by rewrite flows_join (negbTE hi_K).
    rewrite {1}/indist /=.
    case/andP: indist_μ=> [ind1 ind2].
    rewrite (P1 _ _ _ _ _ _ _ _ _ _ ind1 hiL hiL Halloc Halloc2).
    rewrite (P1 _ _ _ _ _ _ _ _ _ _ ind2 hiL hiL Halloc2 Halloc) /=.
    have indist_dfp: indist obs (Vptr (Ptr dfp 0) @ K \_/ K')
                                (Vptr (Ptr dfp2 0) @ K \_/ K').
      by rewrite /indist /= eqxx /= flows_join (negbTE hi_K).
    move: (indist_registerUpdate_aux r3 indist_rs indist_dfp).
    by rewrite upd_r3 upd_r32.
  (* Load *)
  + move=> im μ σ pc C [pv pl] K r r' r1 r2 j LPC v Ll rl rpcl -> /= CODE get_r1 load_p mlab_p [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    case get_r1': registerContent=> [[[|[pv' pl']|] K']|] //=.
    have /= [a] := indist_registerContent indist_s1s2 low_pc1 get_r1.
    rewrite get_r1' => - [<-] {a} /andP [/eqP eK indist_p]; subst K'.
    case get_pv: (Mem.get_frame μ pv) load_p mlab_p => [[fl fr]|] //= load_p [eC].
    subst fl.
    case get_pv': Mem.get_frame=> [[C' fr']|] //=.
    case load_p': nth_error_Z=> [[v' Ll']|] //=.
    rewrite /Vector.nth_order /=.
    case upd_r2': registerUpdate=> [rs2'|] //= [<-] {s2'}.
    move: indist_s1s2 (indist_s1s2).
    rewrite {1}indist_low_pc //= => /and5P [? ind_μ ? /eqP [? ?] ind_rs] indist_s1s2; subst j2 LPC2.
    rewrite /indist /= !flows_join low_pc1 /=.
    apply/and3P; split=> //.
    case: (boolP (isLow K obs)) indist_p => [low_K|hi_K _] /=; last first.
      by apply: indist_cropTop.
    move=> /eqP [??]; subst pv' pl'.
    case: ifPn => [low_C|hi_C]; last first.
      by apply: indist_cropTop.
    have low_pv: isLow (Mem.stamp pv) obs.
      apply: (wf_s1 obs pv pv); last by apply: connect0.
      rewrite /root_set; apply/setUP; left=> /=.
      rewrite /root_set_registers low_pc1.
      by apply: (mframes_from_atoms_nth get_r1 low_K).
    have: indist obs (Mem.get_frame μ pv) (Mem.get_frame μ2 pv).
      case/orP: low_C=> [low_C|low_C].
        case/andP: ind_μ => [/allP/(_ pv) ind _]; apply: ind.
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter all_elems.
        by rewrite low_pv get_pv.
      case/andP: ind_μ => [_ /allP/(_ pv) ind]; rewrite indist_sym; apply: ind.
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter all_elems.
      by rewrite low_pv get_pv'.
    rewrite get_pv get_pv' {1}/indist /= {1}/indist /= => /andP [/eqP ?]; subst C'.
    rewrite orbb in low_C; rewrite low_C /= => ind_fr.
    apply/and3P; split=> //.
    have ind_v: indist obs (v @ Ll) (v' @ Ll').
      move: ind_fr load_p load_p'.
      rewrite /nth_error_Z; case: BinInt.Z.ltb => //.
      elim: fr fr' (BinInt.Z.to_nat pl) {get_pv get_pv'}
            => [|a fr IH] [|a' fr'] //= [|n] //=.
        by rewrite indist_cons => /andP [??] [<-] [<-].
      by rewrite indist_cons => /andP [? /IH]; apply.
    move: (indist_registerUpdate_aux r2 ind_rs ind_v).
    by rewrite upd_r2 upd_r2'.
  (* Store *)
  + move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl lp lf lv -> /= CODE get_r1 get_r2 /= lab_p.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    case: ifP => //; rewrite flows_join; case/andP => low_lp_lf low_LPC_lf [<- <-].
    case get_fp: (Mem.get_frame μ fp) lab_p => // [[lf' fr]] [eq_lf]; subst lf'.
    case upd_i: (update_list_Z fr i (v @ lv)) => [fr'|] // upd_fp low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    case get_r1': registerContent=> [[[|[pv' pl']|] K']|] //=.
    have /= [[v2 K2 get_r2' // /andP [/eqP eK indist_i]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r2.
    subst K2; rewrite get_r2'.
    case get_fp': Mem.get_frame=> [[lf2 fr2]|] //=.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    move: indist_s1s2 (indist_s1s2).
    rewrite {1}indist_low_pc //= => /and5P [? ind_μ ? /eqP [? ?] ind_rs] indist_s1s2; subst j2 LPC2.
    rewrite flows_join; case: ifP => // /andP [low_K' low_lpc'].
    case upd_i': update_list_Z => [fr2'|] //=.
    case upd_fp': Mem.upd_frame => /= [μ2'|] //= [<-] {s2'}.
    rewrite /indist /= low_pc1 /=; apply/and5P; split=> //.
    move: (indist_registerContent_aux r1 ind_rs).
    rewrite get_r1 get_r1' => /andP [/eqP ?]; subst lp.
    case: (boolP (isLow K' obs))=> [low_K'' /eqP [??]|hi_K'' _]; last first.
      have hi_lf: isHigh lf obs by apply: contra hi_K''; apply: flows_trans.
      have hi_lf2: isHigh lf2 obs by apply: contra hi_K''; apply: flows_trans.
      apply/indistMemP=> b low_b.
      rewrite (Mem.get_upd_frame upd_fp) (Mem.get_upd_frame upd_fp').
      case: (altP eqP) => [? _|ne].
        subst b.
        case: (altP eqP)=> [?| ne'].
          subst pv'.
          case/andP: ind_μ=> [/allP/(_ fp) H _].
          move: H.
          rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec mem_filter low_b all_elems /=.
          rewrite get_fp=> /(_ erefl).
          rewrite get_fp' => /andP [/eqP ?]; subst lf2 => _.
          by apply/andP; rewrite eqxx hi_lf2; split.
        case/andP: ind_μ => [/allP/(_ fp) H _].
        move: H.
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        rewrite get_fp=> /(_ erefl).
        case: Mem.get_frame=> [[lf'' fr'']|] // /andP [/eqP <-] _.
        by rewrite /indist /= /indist /= eqxx hi_lf.
      case: (altP eqP)=> [?| ne' def].
        subst b.
        case/andP: ind_μ=> [_ /allP/(_ pv')].
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        rewrite get_fp' indist_sym => /(_ erefl).
        case: Mem.get_frame => [[lf'' fr'']|] //= /andP [/eqP ?] _ _; subst lf''.
        by rewrite /indist /= /indist /= eqxx hi_lf2.
      case/orP: def=> [def|def].
        case/andP: ind_μ=> [/allP/(_ b)].
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        by eauto.
      case/andP: ind_μ=> [_ /allP/(_ b)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      rewrite indist_sym.
      by eauto.
    subst pv' pl'.
    apply/indistMemP=> b low_b.
    rewrite (Mem.get_upd_frame upd_fp) (Mem.get_upd_frame upd_fp').
    case: (altP eqP) => [? _|ne].
      subst b.
      case/andP: ind_μ => [/allP/(_ fp)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      rewrite get_fp get_fp' => /(_ erefl) /andP [/eqP ? ind_fr] _; subst lf2.
      apply/andP; split=>//.
      case: (boolP (isLow lf obs)) ind_fr=> //= low_lf.
      move: upd_i upd_i'; rewrite /update_list_Z.
      case: ifP=> // _.
      elim: fr fr2 fr' fr2' {i get_fp get_fp' get_r1 get_r1' upd_fp upd_fp'} (BinInt.Z.to_nat i)
            => [|v1 fr1 IH] [|v2' fr2] fr1' fr2' [|i] //=.
        move=> [<-] [<-].
        rewrite !indist_cons=> /andP [i_v i_fr].
        apply/andP; split=> //.
        by rewrite /indist /= eqxx.
      case upd1: update_list=> [fr1''|] //=.
      case upd2: update_list=> [fr2''|] //= [<-] [<-].
      rewrite !indist_cons=> /andP [->] /=.
      by eauto.
    case/orP=> [def|def].
      case/andP: ind_μ=> [/allP/(_ b)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      by eauto.
    case/andP: ind_μ=> [_ /allP/(_ b)].
    rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
    rewrite indist_sym.
    by eauto.
  (* Write *)
  + move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl v' lp lv lv' lf -> /= CODE get_r1 get_r2 /= load_fp lab_fp.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    case: ifP => //; rewrite !flows_join=> /andP [/andP [low_LPC low_lp] low_lv] [<- <-].
    case get_fp: (Mem.get_frame μ fp) load_fp lab_fp => // [[lf' fr]] load_fp [eq_lf]; subst lf'.
    case upd_i: (update_list_Z fr i (v @ lv')) => [fr'|] // upd_fp low_pc1 indist_s1s2.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    case get_r1': registerContent=> [[[|[pv' pl']|] K']|] //=.
    have /= [[v2 K2 get_r2' // /andP [/eqP eK indist_i]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r2.
    subst K2; rewrite get_r2'.
    case get_fp': Mem.get_frame=> [[lf2 fr2]|] //=.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    move: indist_s1s2 (indist_s1s2).
    rewrite {1}indist_low_pc //= => /and5P [? ind_μ ? /eqP [? ?] ind_rs] indist_s1s2; subst j2 LPC2.
    move=> wf_s1.
    case load_fp': nth_error_Z => [[v2' lv2']|] //=.
    rewrite !flows_join; case: ifP => // /andP [/andP [low_lpc' low_K'] low_lv'].
    case upd_i': update_list_Z => [fr2'|] //=.
    case upd_fp': Mem.upd_frame => /= [μ2'|] //= [<-] {s2'}.
    rewrite /indist /= low_pc1 /=; apply/and5P; split=> //.
    move: (indist_registerContent_aux r1 ind_rs).
    rewrite get_r1 get_r1' => /andP [/eqP ?]; subst lp.
    case: (boolP (isLow K' obs))=> [low_K'' /eqP [??]|hi_K'' _]; last first.
      have hi_lf: isHigh (lf \_/ lv') obs by apply: contra hi_K''; apply: flows_trans.
      have hi_lf2: isHigh (lf2 \_/ lv2') obs by apply: contra hi_K''; apply: flows_trans.
      apply/indistMemP=> b low_b.
      rewrite (Mem.get_upd_frame upd_fp) (Mem.get_upd_frame upd_fp').
      case: (altP eqP) => [? _|ne].
        subst b.
        case: (altP eqP)=> [?| ne'].
          subst pv'.
          case/andP: ind_μ=> [/allP/(_ fp) H _].
          move: H.
          rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec mem_filter low_b all_elems /=.
          rewrite get_fp=> /(_ erefl).
          rewrite get_fp' => /andP [/eqP ?]; subst lf2 => ind_fr.
          rewrite /indist /= /indist /= eqxx /=.
          move: hi_lf hi_lf2 ind_fr.
          rewrite !flows_join.
          case: (boolP (isLow lf obs))=> [low_lf|hi_lf] //= hi_lv' hi_lv2'.
          move: upd_i upd_i' load_fp load_fp'.
          rewrite /update_list_Z /nth_error_Z.
          case: ifP=> //= _.
          case: ifP=> //= _.
          { elim: fr fr2 fr' fr2' {get_fp get_fp' upd_fp upd_fp' i pl' get_r1 get_r1'}
                  (BinInt.Z.to_nat i) (BinInt.Z.to_nat pl')
                  => [|[v1 lv1] fr1 IH] [|[v2'' lv2''] fr2] fr1' fr2' [|n1] [|n2] //=.
          * move=> [<-] [<-] [-> ->] [-> ->].
            rewrite !indist_cons => /andP [ind ->]; rewrite andbT.
            case/andP: ind=> [/eqP ?]; subst lv2'.
            by rewrite /indist /= hi_lv2' eqxx.
          * move=> [<-].
            case upd: update_list=> [fr2''|] //= [<-] [-> ->] n.
            rewrite !indist_cons.
            case/andP=> [/andP [/eqP ?]]; subst lv2''.
            rewrite {3}/indist /= eqxx hi_lv' /= => _.
            elim: fr2 fr1 fr2'' n2 upd n {v1 lv1 IH}=> [|v2''' fr2 IH] [|[v1 lv1] fr1] fr2'' [|n2] //=.
              move=> [<-] [->].
              rewrite !indist_cons=> /andP [ind ->]; rewrite andbT.
              move: ind; rewrite /indist /= => /andP [/eqP ?]; subst lv2'.
              by rewrite eqxx hi_lv2'.
            case upd: update_list=> [fr2'''|] //= [<-] Hn.
            rewrite !indist_cons => /andP [->] /=.
            by apply: IH upd Hn.
          * case upd: update_list=> [fr1''|] //= [<-] [<-] Hn [-> ->].
            rewrite !indist_cons.
            case/andP=> [/andP [/eqP ?]]; subst lv2'.
            rewrite {3}/indist /= eqxx hi_lv2' /= => _.
            elim: fr1 fr2 fr1'' n1 upd Hn {v1 v2 indist_i get_r2 get_r2' IH}=>
                  [|v1 fr1 IH] [|[v2 lv2] fr2] fr1'' [|n2] //=.
              move=> [<-] [->].
              rewrite !indist_cons=> /andP [ind ->]; rewrite andbT.
              move: ind; rewrite /indist /= => /andP [/eqP ?]; subst lv'.
              by rewrite eqxx hi_lv'.
            case upd: update_list=> [fr2'''|] //= [<-] Hn.
            rewrite !indist_cons => /andP [->] /=.
            by apply: IH upd Hn.
          * case upd1: update_list=> [fr1''|] //= [<-].
            case upd2: update_list=> [fr2''|] //= [<-] nth1 nth2.
            rewrite !indist_cons => /andP [->] /=.
            by eauto. }
        case/andP: ind_μ => [/allP/(_ fp) H _].
        move: H.
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        rewrite get_fp=> /(_ erefl).
        case: Mem.get_frame=> [[lf'' fr'']|] // /andP [/eqP <-] ind_fr.
        rewrite /indist /= /indist /= eqxx /=.
        rewrite -implybE; apply/implyP => low_lf.
        move: hi_lf; rewrite flows_join low_lf /= => hi_lv'.
        move: ind_fr; rewrite low_lf /=.
        { move: upd_i load_fp.
          rewrite /update_list_Z /nth_error_Z.
          case: ifP=> //= _.
          elim: fr fr' fr'' (BinInt.Z.to_nat i) {get_fp upd_fp}
                => [|v1 fr1 IH] fr' [|v2'' fr2''] [|n] //=.
            move=> [<-] [->].
            rewrite !indist_cons => /andP [ind ->]; rewrite andbT.
            case: v2'' ind=> [??].
            rewrite /indist /= => /andP [/eqP <-]; rewrite eqxx.
            by rewrite hi_lv'.
          case upd: update_list=> [fr1'|] //= [<-] Hn.
          rewrite !indist_cons => /andP [->] /=.
          by eauto. }
      case: (altP eqP)=> [?| ne' def].
        subst b.
        case/andP: ind_μ=> [_ /allP/(_ pv')].
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        rewrite get_fp' indist_sym => /(_ erefl).
        case: Mem.get_frame => [[lf'' fr'']|] //= /andP [/eqP ?] ind_fr _; subst lf''.
        rewrite /indist /= /indist /= eqxx /=.
        rewrite -implybE; apply/implyP => low_lf.
        move: hi_lf2; rewrite flows_join low_lf /= => hi_lv2'.
        move: ind_fr; rewrite low_lf /=.
        { move: upd_i' load_fp'.
          rewrite /update_list_Z /nth_error_Z.
          case: ifP=> //= _.
          elim: fr2 fr2' fr'' (BinInt.Z.to_nat pl') {get_fp' upd_fp'}
                => [|v1 fr1 IH] fr'' [|v2'' fr2''] [|n] //=.
            move=> [<-] [->].
            rewrite !indist_cons => /andP [ind ->]; rewrite andbT.
            case: v2'' ind=> [v2'' v2l''].
            rewrite /indist /= => /andP [/eqP ?]; subst v2l''; rewrite eqxx /=.
            by rewrite hi_lv2'.
          case upd: update_list=> [fr1'|] //= [<-] Hn.
          rewrite !indist_cons => /andP [->] /=.
          by eauto. }
      case/orP: def=> [def|def].
        case/andP: ind_μ=> [/allP/(_ b)].
        rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
        by eauto.
      case/andP: ind_μ=> [_ /allP/(_ b)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      rewrite indist_sym.
      by eauto.
    subst pv' pl'.
    apply/indistMemP=> b low_b.
    rewrite (Mem.get_upd_frame upd_fp) (Mem.get_upd_frame upd_fp').
    case: (altP eqP) => [? _|ne].
      subst b.
      case/andP: ind_μ => [/allP/(_ fp)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      rewrite get_fp get_fp' => /(_ erefl) /andP [/eqP ? ind_fr] _; subst lf2.
      apply/andP; split=>//.
      case: (boolP (isLow lf obs)) ind_fr=> //= low_lf.
      move: upd_i upd_i'; rewrite /update_list_Z.
      move: load_fp load_fp'; rewrite /nth_error_Z.
      case: ifP=> // _.
      elim: fr fr2 fr' fr2' {i get_fp get_fp' get_r1 get_r1' upd_fp upd_fp'} (BinInt.Z.to_nat i)
            => [|v1 fr1 IH] [|v2'' fr2] fr1' fr2' [|i] //=.
        move=> [->] [->] [<-] [<-].
        rewrite !indist_cons=> /andP [i_v i_fr].
        apply/andP; split=> //.
        case/andP: i_v => /eqP? i_v; subst lv2'.
        apply/andP; split=> //.
        case: (boolP (isLow lv' obs)) i_v => //= low_lv'_obs indist_v'.
        case/orP: indist_i => [high_lv | //].
        have low_lf_lv': isLow (lf \_/ lv') obs by rewrite flows_join low_lf.
        move/negP in high_lv; contradict high_lv.
        eapply flows_trans; eassumption.
      case upd1: update_list=> [fr1''|] //=.
      case upd2: update_list=> [fr2''|] //= ? ? [<-] [<-].
      rewrite !indist_cons=> /andP [->] /=.
      by eauto.
    case/orP=> [def|def].
      case/andP: ind_μ=> [/allP/(_ b)].
      rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
      by eauto.
    case/andP: ind_μ=> [_ /allP/(_ b)].
    rewrite /blocks_stamped_below -Mem.get_blocks_spec /allThingsBelow mem_filter low_b all_elems /=.
    rewrite indist_sym.
    by eauto.
  (* Jump *)
  + move=> im μ σ pc addr Ll r r1 j LPC rpcl -> /= CODE get_r1 [<-] low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    have /= [[[] // addr2 K2 -> // /andP [/eqP <- indist_i]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    move=> [<-].
    move: indist_s1s2; rewrite /Vector.nth_order /= indist_low_pc //=.
    case/and5P=> [? ? ? /eqP [_ ?] ?]; subst LPC2.
    rewrite /indist /= flows_join low_pc1 /=.
    case: (boolP (isLow _ _)) indist_i => [low|high _] //=.
      by move=> /eqP [->]; rewrite eqxx /=; apply/and4P; split.
    apply/and3P; split=> //.
    by apply: indist_cropTop.
  (* BNZ *)
  + move=> im μ σ pc n m K r r1 j LPC rpcl -> /= CODE get_r1 [<-] low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    have /= [[[] // m2 K2 -> // /andP [/eqP <- indist_i]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    move=> [<-] {s2'}.
    move: indist_s1s2; rewrite /Vector.nth_order /= indist_low_pc //= => ind.
    case/and5P: ind wf_s2=> [? ? ? /eqP [<- {j2} ?] ?] wf_s2; subst LPC2.
    rewrite /indist /= flows_join low_pc1 /=.
    case: (boolP (isLow _ _)) indist_i => [low|high _] //=.
      by move=> /eqP [->]; rewrite eqxx /=; apply/and4P; split.
    apply/and3P; split=> //.
    by apply: indist_cropTop.
  (* PSetOff *)
  + move=> im μ σ pc fp' j K1 n K1' r r' r1 r2 r3 j' LPC rl rpcl -> /= CODE get_r1 get_r2 [<- <-].
    rewrite /Vector.nth_order /= => upd_r3 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    have /= [[[] // m2 K2 -> // /andP [/eqP <- indist_m]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    case: m2 indist_m => [fp2' j2'] //= indist_p.
    have /= [[[] // n2 K2' -> // /andP [/eqP <- indist_n]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r2.
    move: indist_s1s2; rewrite indist_low_pc //= => /and5P [? ? ? /eqP [<- <-] ind_rs].
    rewrite /Vector.nth_order /=.
    case upd_r3': registerUpdate=> [r2'|] //= [<-] {s2'}.
    have [l|h] := boolP (isLow (K1 \_/ K1') obs).
      move: (l) indist_p indist_n upd_r3'.
      rewrite flows_join => /andP [-> ->] /= /eqP [<- _] /eqP [<-] {fp2' j2' n2} upd_r3'.
      rewrite /indist /= low_pc1 /=.
      apply/and5P; split=> //.
      have indist_v: indist obs (Vptr (Ptr fp' n) @ K1 \_/ K1') (Vptr (Ptr fp' n) @ K1 \_/ K1').
        by rewrite indistxx.
      move: (indist_registerUpdate_aux r3 ind_rs indist_v).
      by rewrite upd_r3 upd_r3'.
    rewrite /indist /= low_pc1 /=; apply/and5P; split=> //.
    have indist_v: indist obs (Vptr (Ptr fp' n) @ K1 \_/ K1') (Vptr (Ptr fp2' n2) @ K1 \_/ K1').
      by rewrite /indist /= eqxx h.
    move: (indist_registerUpdate_aux r3 ind_rs indist_v).
    by rewrite upd_r3 upd_r3'.
  (* Put *)
  + move=> im μ σ pc x r r' r1 j LPC rl rpcl -> /= CODE [<- <-] upd_r1 low_pc1.
    move=> indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    have /= [regs2' -> indist_rs /= [<-]] :=
      indist_registerUpdate indist_s1s2 low_pc1 (indistxx (Vint x @ ⊥)) upd_r1.
    move: (indist_pc indist_s1s2 low_pc1)=> /= [??]; subst j2 LPC2.
    move: indist_s1s2; rewrite indist_low_pc // /= indist_low_pc // /=.
    by case/and5P=> [?????]; apply/and5P; split=> //.
  (* BinOp *)
  + move=> im μ σ pc o v1 L1 v2 L2 v r r1 r2 r3 r' j LPC rl rpcl -> /= CODE get_r1 get_r2 [<- <-] eval.
    rewrite /Vector.nth_order /= => upd_r3 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2
          => [im2 μ2 σ2 rs2 [j2 LPC2]] //= wf_s2 indist_s1s2.
    have /= [[v1' K2 -> // /andP [/eqP <- indist_v1]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    have /= [[v2' K2' -> // /andP [/eqP <- indist_v2]]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r2.
    case eval': eval_binop=> [v'|] //=.
    rewrite /Vector.nth_order /=.
    move: indist_s1s2; rewrite indist_low_pc //= => /and5P [? ? ? /eqP [<- <-] ind_rs].
    case upd_r3': registerUpdate=> [r2'|] //= [<-] {s2'}.
    have [l|h] := boolP (isLow (L1 \_/ L2) obs).
      move: (l) indist_v1 indist_v2 eval' upd_r3'.
      rewrite flows_join => /andP [-> ->] /= /eqP <- /eqP <- {v1' v2'}.
      rewrite eval => - [<-] upd_r3'.
      rewrite /indist /= low_pc1 /=.
      apply/and5P; split=> //.
      have indist_v : indist obs (v @ L1 \_/ L2) (v @ L1 \_/ L2) by rewrite indistxx.
      move: (indist_registerUpdate_aux r3 ind_rs indist_v).
      by rewrite upd_r3 upd_r3'.
    rewrite /indist /= low_pc1 /=; apply/and5P; split=> //.
    have indist_v: indist obs (v @ L1 \_/ L2) (v' @ L1 \_/ L2).
      by rewrite /indist /= eqxx h.
    move: (indist_registerUpdate_aux r3 ind_rs indist_v).
    by rewrite upd_r3 upd_r3'.
  (* Nop *)
  + move=> im μ σ pc r j LPC rpcl -> /= CODE [<-] low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2 low_pc1) /state_instr_lookup /= CODE /=.
    case: s2 wf_s2 indist_s1s2 => [im2 μ2 σ2 rs2 [j2 LPC2]] wf_s2 indist_s1s2 [<-].
    move: indist_s1s2; rewrite !indist_low_pc //=
      => /and5P [indist_im indist_μ indist_σ /eqP[<- <-] indist_r].
    by apply/and5P.
  (* MSize *)
  + move=> im μ σ pc [b off] K C rs r' r1 r2 j LPC rl rpcl n -> /= CODE get_r1 lab_p [<- <-] size_p.
    rewrite /Vector.nth_order /= => upd_r2 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => [im2 μ2 σ2 rs2 [j2 LPC2]] wf_s2 indist_s1s2.
    have /= [[v1' K2] -> /andP [/eqP <- indist_v1]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    case: v1' indist_v1 => [] // [b' off'] /= indist_p'.
    move get_frame_b: (Mem.get_frame μ b) lab_p size_p => [[lab fr]|//] [?] [?]; subst lab n.
    case get_frame_b': (Mem.get_frame μ2 b') => //= [[C' fr']] /=.
    rewrite /Vector.nth_order /=.
    case upd_r2': (registerUpdate rs2 r2 _) => //= [r2'].
    case: s2' => im2' μ2' σ2' r2'' pc2' [<- <- <- <- <-]; clear im2' μ2' σ2' r2'' pc2'.
    move: indist_s1s2; rewrite indist_low_pc //=
      => /and5P [indist_im indist_μ indist_σ /eqP[? ?] indist_rs]; subst j2 LPC2.
    have [l|h] := boolP (isLow (LPC \_/ K) obs).
    * rewrite /indist /= l /=; apply/and5P; split=>//.
      have indist_ints : indist obs (Vint (BinInt.Z.of_nat (Datatypes.length fr))  @ C)
                                    (Vint (BinInt.Z.of_nat (Datatypes.length fr')) @ C'). {
        move: l; rewrite flows_join => /andP [low_LPC low_K].
        move: indist_p' => /orP [h|]; first by move/negP in h.
        rewrite {1}/indist /= => /eqP [] *; subst b' off'.
        move: indist_μ; rewrite {1}/indist /= /indistMemAsym
          => /andP [/allP/(_ b) indist_get _].
        have bsb: b \in blocks_stamped_below obs μ. {
          rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec mem_filter.
          rewrite get_frame_b all_elems /= !andbT.
          move: wf_s1; rewrite /well_stamped /well_stamped_label => wf_s1.
          apply wf_s1 with (f1 := b) => /=.
          - rewrite in_setU /=; apply/orP; left.
            by apply (root_set_registers_nth get_r1).
          - by rewrite /reachable; apply connect0.
        }
        move: indist_get => /(_ bsb).
        rewrite /indist /= /indist /= get_frame_b get_frame_b'
          => /andP [eq_C /orP [high_C | indist_fr]];
          apply/andP; split=>//.
        - by rewrite high_C.
        - apply/orP; right; apply/eqP; do 2 f_equal.
          by move: indist_fr; rewrite /indist /= => /andP [/eqP? _].
      }
      move: (indist_registerUpdate_aux r2 indist_rs indist_ints).
      by rewrite {1}/indist /= upd_r2 upd_r2'.
    * rewrite /indist /= (negbTE h) /=; apply/and3P; split=>//.
      by apply indist_cropTop.
  (* PGetOff *)
  + move=> im μ σ pc fp' j K rs r' r1 r2 j' LPC rl rpcl -> /= CODE get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2) /state_instr_lookup //= CODE /=.
    case: s2 wf_s2 indist_s1s2 => [im2 μ2 σ2 rs2 [j2 LPC2]] wf_s2 indist_s1s2.
    have /= [[v1' K2] -> /andP [/eqP <- indist_v1]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    case: v1' indist_v1 => [] // [fp2' j2'] /= indist_ptr.
    have indist_atom : indist obs ((Vint j')@K) ((Vint j2')@K). {
      rewrite /indist /= eqxx /=.
      move: indist_ptr => /orP [-> // | ].
      by rewrite /indist /= => /eqP [_ ->]; rewrite eqxx orbT.
    }
    rewrite /Vector.nth_order /=.
    have /= [r2' -> indist_r] /= :=
      indist_registerUpdate indist_s1s2 low_pc1 indist_atom upd_r2.
    case: s2' => im2' μ2' σ2' rs2' pc2' [<- <- <- <- <-]; clear im2' μ2' σ2' rs2' pc2'.
    move: indist_s1s2; rewrite !indist_low_pc //=
      => /and5P [indist_im indist_μ indist_σ /eqP[<- <-] indist_rs].
    by apply/and5P.
  (* Mov *)
  + move=> im μ σ v K pc rs r' r1 r2 j LPC rl rpcl -> /= CODE get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 low_pc1 indist_s1s2 wf_s1.
    rewrite /fstep -(indist_instr indist_s1s2 low_pc1) /state_instr_lookup /= CODE /=.
    case: s2 wf_s2 indist_s1s2 => [im2 μ2 σ2 rs2 [j2 LPC2]] wf_s2 indist_s1s2.
    have /= [[v' K'] -> /andP [/eqP <- indist_v]] :=
      indist_registerContent indist_s1s2 low_pc1 get_r1.
    rewrite /Vector.nth_order /=.
    have indist_vK : indist obs (v@K) (v'@K) by rewrite /indist /= eqxx indist_v.
    have /= [r2' -> indist_r] /= :=
      indist_registerUpdate indist_s1s2 low_pc1 indist_vK upd_r2.
    case: s2' => im2' μ2' σ2' rs2' pc2' [<- <- <- <- <-]; clear im2' μ2' σ2' rs2' pc2'.
    move: indist_s1s2; rewrite !indist_low_pc //=
      => /and5P [indist_im indist_μ indist_σ /eqP[<- <-] indist_rs].
    by apply/and5P.
- case: step1 high_pc1 high_pc2.
  (* Lab *)
  + move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> /= instr get_r1 [<- <-] upd_r2 high_pc.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* PcLab *)
  + move=> im μ σ pc r r' r1 j LPC rl rpcl -> /= CODE [<- <-] upd_r1 high_pc.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* MLab *)
  + move=> im μ σ pc r r1 r2 p K C j LPC rl r' rpcl -> CODE ? get_r1 [].
    rewrite /Vector.nth_order /= => <- <- upd_r2 high_pc.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* PutLab *)
  + move=> im μ σ pc r r' r1 j LPC rl rpcl l' -> /= CODE [<- <-] upd_r1 high_pc.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* Call *)
  + move=> im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl -> /= CODE get_r1 get_r2 [<- <-].
    rewrite /Vector.nth_order /= => high_pc.
    by rewrite /indist /= /cropTop /= !flows_join (negbTE high_pc) !andbF /= !indistxx /=.
  (* BRet *)
  + move=> im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl -> -> /= CODE get_r1.
    rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
    case: ifPn=> // Hjoins [<- <-] upd_r1 high_pc high_pc'.
    by rewrite /indist /= /cropTop /= (negbTE high_pc) (negbTE high_pc') /= !indistxx.
  (* Alloc *)
  + move=> im μ μ' σ pc r r' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp -> /= CODE get_r1 get_r2 [<- <-].
    rewrite /Vector.nth_order /= => alloc_i upd_r3 high_pc _.
    rewrite /indist /= (negbTE high_pc) /= !indistxx andbT /=.
    move: alloc_i get_r1; rewrite /alloc /zreplicate.
    case: ZArith_dec.Z_lt_dec=> [//|Pi] /=.
    have {Pi} Pi: BinInt.Z.le 0 i by omega.
    rewrite -{2}(Znat.Z2Nat.id _ Pi) {Pi}.
    move: (BinInt.Z.to_nat i) => {i} i [alloc_i] get_r1.
    have high_L: isHigh (K \_/ (K' \_/ LPC)) o by rewrite !flows_join (negbTE high_pc) !andbF.
    apply/andP; split; apply/allP=> /= b;
    rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec
            mem_filter all_elems andbT (Mem.alloc_get_frame alloc_i);
    have [<-{b}|ne] := altP eqP;
    by rewrite ?indistxx // (Mem.alloc_stamp alloc_i) (negbTE high_L).
  (* Load *)
  + move=> im μ σ pc C [pv pl] K r r' r1 r2 j LPC v Ll rl rpcl -> ? get_r1 load_p mlab_p [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 high_pc.
    by rewrite /indist /= !flows_join (negbTE high_pc) /= !indistxx.
  (* Store *)
  + move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl lp lf lv -> ? get_r1 get_r2 /= lab_p.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    case: ifP => //; rewrite flows_join; case/andP => low_lp_lf low_LPC_lf [<- <-].
    case get_fp: (Mem.get_frame μ fp) lab_p => // [[lf' fr]] [eq_lf].
    rewrite {}eq_lf {lf'} in get_fp *.
    case upd_i: (update_list_Z fr i (v @ lv)) => [fr'|] // upd_fp high_pc _.
    rewrite /indist /= (negbTE high_pc) /= 2!indistxx andbT /=.
    apply/andP; split; apply/allP=> /= b;
    rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec
            mem_filter all_elems andbT (Mem.get_upd_frame upd_fp);
    have [<-{b}|ne] := altP eqP;
    rewrite ?get_fp /= ?indistxx // andbT /indist /= /indist /= eqxx /= -implybE => _;
    apply/implyP => low_lf;
    by move: high_pc; rewrite (flows_trans _ _ _ low_LPC_lf low_lf).
  (* Write *)
  + move=> im μ σ pc v [fp i] μ' r r1 r2 j LPC rpcl rl v' lp lv lv' lf -> ? get_r1 get_r2 /= load_fp lab_fp.
    rewrite /run_tmr /= /apply_rule /= /Vector.nth_order /=.
    case: ifP => //; rewrite !flows_join=> /andP [/andP [low_LPC low_lp] low_lv] [<- <-].
    case get_fp: (Mem.get_frame μ fp) load_fp lab_fp => // [[lf' fr]] load_fp [eq_lf].
    rewrite {}eq_lf {lf'} in get_fp *.
    case upd_i: (update_list_Z fr i (v @ lv')) => [fr'|] // upd_fp high_pc _.
    rewrite /indist /= (negbTE high_pc) /= 2!indistxx andbT /=.
    have ind_fr: indist o (Fr lf fr) (Fr lf fr').
      rewrite /indist /= eqxx /= -implybE; apply/implyP=> low_lf.
      have: isHigh (lf \_/ lv') o.
        by apply: contra high_pc; apply: flows_trans.
      rewrite flows_join low_lf /= => high_lv'.
      move: load_fp upd_i {get_r1}; rewrite /nth_error_Z /update_list_Z.
      case: ifP=> // _; move: {i} (BinInt.Z.to_nat i).
      elim: fr fr' {get_fp upd_fp}=> [|[v1 lv1] fr1 IH] fr2 [|n] //=.
        move=> [-> ->] [<-] {fr2}; rewrite indist_cons indistxx andbT.
        by rewrite /indist /= eqxx high_lv'.
      case upd_fr1: update_list => [fr2'|] //= get_n [<-] {fr2}.
      by rewrite indist_cons indistxx /=; eauto.
    apply/andP; split; apply/allP=> /= b;
    rewrite /blocks_stamped_below /allThingsBelow -Mem.get_blocks_spec
            mem_filter all_elems andbT (Mem.get_upd_frame upd_fp);
    have [<-{b}|ne] := altP eqP;
    by rewrite ?get_fp /= ?indistxx // andbT /indist /= indist_sym.
  (* Jump *)
  + move=> im μ σ pc addr Ll r r1 j LPC rpcl -> ? get_r1 [<-] /= high_pc high_pc'.
    by rewrite /indist /= (negbTE high_pc) (negbTE high_pc') /= !indistxx.
  (* BNZ *)
  + move=> im μ σ pc n m K r r1 j LPC rpcl -> ? get_r1 [<-] /= high_pc high_pc'.
    by rewrite /indist /= (negbTE high_pc) (negbTE high_pc') /= !indistxx.
  (* PSetOff *)
  + move=> im μ σ pc fp' j K1 n K2 r r' r1 r2 r3 j' LPC rl rpcl -> ? get_r1 get_r2 [<- <-].
    rewrite /Vector.nth_order /= => upd_r3 high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* Put *)
  + move=> im μ σ pc x r r' r1 j LPC rl rpcl -> ? [<- <-] upd_r1 /= high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* BinOp *)
  + move=> im μ σ pc op v1 L1 v2 L2 v r r1 r2 r3 r' j LPC rl rpcl -> _ get_r1 get_r2 [<- <-] eval.
    rewrite /Vector.nth_order /= => upd_r3 high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* Nop *)
  + move=> im μ σ pc r j LPC rpcl -> _ [<-] /= high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* MSize *)
  + move=> im μ σ pc p K C r r' r1 r2 j LPC rl rpcl n -> _ get_r1 lab_p [<- <-] size_p.
    rewrite /Vector.nth_order /= => upd_r2 high_pc high_pc'.
    by rewrite /indist /= (negbTE high_pc) (negbTE high_pc') /= !indistxx.
  (* PGetOff *)
  + move=> im μ σ pc fp' j K r r' r1 r2 j' LPC rl rpcl -> _ get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
  (* Mov *)
  + move=> im μ σ v K pc r r' r1 r2 j LPC rl rpcl -> _ get_r1 [<- <-].
    rewrite /Vector.nth_order /= => upd_r2 high_pc _.
    by rewrite /indist /= (negbTE high_pc) /= !indistxx.
- move/fstepP in step1.
  have high_pc2: isHigh ∂(st_pc s2) o by rewrite -(indist_pcl indist_s1s2).
  move=> step2.
  move: (high_low step1 high_pc1 low_pc1') (high_low step2 high_pc2 low_pc2') => i1 i2.
  move: step1 step2; rewrite /fstep i1 i2 /=.
  case: s1 s2 high_pc1 high_pc2 wf_s1 wf_s2 indist_s1s2 {i1 i2}
        => [im1 μ1 [[|[[pc1' LPC1'] rs1' r1' B1] σ1]] rs1 [pc1 LPC1]] //=
           [im2 μ2 [[|[[pc2' LPC2'] rs2' r2' B2] σ2]] rs2 [pc2 LPC2]] //=
           high_pc1 high_pc2 wf_s1 wf_s2.
  rewrite {1}/indist /= (negbTE high_pc1) (negbTE high_pc2) /= => indist_s1s2.
  case get_r1': registerContent=> [[a1 R1]|] //=.
  case get_r2': registerContent=> [[a2 R2]|] //=.
  rewrite /run_tmr /apply_rule /= /Vector.nth_order /=.
  case: ifP=> //= guard1; case: ifP=> //= guard2.
  case upd_r1': registerUpdate=> [rs1''|] //= [e1].
  case upd_r2': registerUpdate=> [rs2''|] //= [e2].
  move: low_pc1' low_pc2'; rewrite -{}e1 -{}e2 {s1' s2'} /= => low_pc1' low_pc2'.
  move: indist_s1s2; rewrite /cropTop /= low_pc1' low_pc2' indist_cons {3}/indist /= low_pc1' /=.
  case/and4P => [ind_im ind_μ ind_p ind_σ].
  case/and4P: ind_p wf_s2 guard2 low_pc2' get_r2' upd_r2'
              => [/eqP [<- <-] ind_rs /eqP <- /eqP <-]
                 wf_s2 guard2 low_pc2' get_r2' upd_r2' {pc2' LPC2' r2' B2}.
  rewrite /indist /= low_pc1' /= ind_im ind_μ eqxx {1}/indist /= ind_σ /=.
  have ind_r: indist o (a1 @ B1) (a2 @ B1).
    rewrite /indist /= eqxx /= -implybE; apply/implyP=> low_B.
    have low: isLow (B1 \_/ LPC1') o by rewrite flows_join low_B.
    move: (flows_trans _ _ _ guard1 low).
    by rewrite flows_join (negbTE high_pc1) andbF.
  move: (indist_registerUpdate_aux r1' ind_rs ind_r).
  by rewrite upd_r1' upd_r2'.
Qed.

End NIProof.
