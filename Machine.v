Require Import ZArith.
Require Import List.
Require Import EquivDec.

Require Import Utils. Import DoNotation.
Require Import Labels.
Require Import Rules.
Require Import Memory.
Require Import Instructions.

(** Rule Table *)

Local Open Scope nat.
Definition labelCount (c:OpCode) : nat :=
  match c with
  | OpLab     => 0
  | OpMLab    => 2
  | OpPcLab   => 0
  | OpBCall   => 2
  | OpBRet    => 3
  | OpPutLab  => 0
  | OpNop     => 0
  | OpPut     => 0
  | OpBinOp   => 2
  | OpJump    => 1
  | OpBNZ     => 1
  | OpLoad    => 3
  | OpStore   => 3
  | OpWrite   => 4
  | OpAlloc   => 3
  | OpPSetOff => 2
  | OpPGetOff => 1
  | OpMSize   => 2
  | OpMov     => 1
end.

Definition table := forall op, AllowModify (labelCount op).

Definition default_table : table := fun op =>
  match op with
  | OpLab     =>  ≪ TRUE , BOT , LabPC ≫
  | OpMLab    =>  ≪ TRUE , Lab1 , LabPC ≫
  | OpPcLab   =>  ≪ TRUE , BOT , LabPC ≫
  | OpBCall   =>  ≪ TRUE , JOIN Lab2 LabPC , JOIN Lab1 LabPC ≫
  | OpBRet    =>  ≪ LE (JOIN Lab1 LabPC) (JOIN Lab2 Lab3) , Lab2 , Lab3 ≫
  | OpPutLab  =>  ≪ TRUE , BOT , LabPC ≫
  | OpNop     =>  ≪ TRUE , __ , LabPC ≫
  | OpPut     =>  ≪ TRUE , BOT , LabPC ≫
  | OpBinOp   =>  ≪ TRUE , JOIN Lab1 Lab2, LabPC ≫
  | OpJump    =>  ≪ TRUE , __ , JOIN LabPC Lab1 ≫
  | OpBNZ     =>  ≪ TRUE , __ , JOIN Lab1 LabPC ≫
  | OpLoad    =>  ≪ TRUE , Lab3 , JOIN LabPC (JOIN Lab1 Lab2) ≫
  | OpStore   =>  ≪ LE (JOIN Lab1 LabPC) Lab2 , Lab3 , LabPC ≫
  | OpWrite   =>  ≪ LE (JOIN (JOIN LabPC Lab1) Lab3)
                        (JOIN Lab2 Lab4), Lab4, LabPC ≫
  | OpAlloc   =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫
  | OpPSetOff =>  ≪ TRUE , JOIN Lab1 Lab2 , LabPC ≫
  | OpPGetOff =>  ≪ TRUE , Lab1 , LabPC ≫
  | OpMSize   =>  ≪ TRUE , Lab2 , JOIN LabPC Lab1 ≫
  | OpMov     =>  ≪ TRUE , Lab1 , LabPC ≫
end.

Module Type FINLAT.
  Parameter Label : Type.
  Parameter FLat  : FiniteLattice Label.
End FINLAT.

Module MachineM (Lab : FINLAT).
Export Lab.

(** memory frame pointers. *)
Definition mframe : Type := Mem.block Label.

(* values *)
Inductive Pointer : Type :=
  | Ptr (fp:mframe) (i:Z).

Inductive Value : Type :=
  | Vint  (n:Z)
  | Vptr  (p:Pointer)
  | Vlab  (l:Label).

Inductive Atom : Type :=
 | Atm (v:Value) (l:Label).

Infix "@" := Atm (no associativity, at level 50).

Inductive Ptr_atom : Type :=
 | PAtm (i:Z) (l:Label).

Definition label_eq (l1 l2 : Label) := (flows l1 l2 && flows l2 l1)%bool.

Definition pc_eq (pc1 pc2 : Ptr_atom) : bool :=
  match pc1, pc2 with
  | PAtm i1 l1, PAtm i2 l2 => (Z_eq i1 i2 && label_eq l1 l2)%bool
  end.

Definition imem := list (@Instr Label).

Definition instr_lookup (m:imem) (pc:Ptr_atom) : option (@Instr Label) :=
  let '(PAtm i _) := pc in
  nth_error_Z m i.
Notation "m [ pc ]" := (instr_lookup m pc) (at level 20).

Definition add_pc (pc:Ptr_atom) (n:Z) : Ptr_atom :=
  let '(PAtm i l) := pc in
  PAtm (Zplus i n) l.
Infix "+" := add_pc.

Definition pc_lab (pc:Ptr_atom) : Label :=
  let '(PAtm _ l) := pc in l.
Notation "'∂' pc" := (pc_lab pc) (at level 0).

Definition atom_lab (a : Atom) : Label :=
  let '(Atm _ l) := a in l.

(* Registers *)
Definition register := Atom.
Definition regSet := list register.

(* Stack *)
Record StackFrame := SF {
  sf_return_addr : Ptr_atom;
  sf_saved_regs : regSet;
  sf_result_reg : regId;
  sf_result_lab : Label
}.

Inductive Stack : Type := ST : list StackFrame -> Stack.
Definition unStack s := let 'ST xs := s in xs.

Class Join (t :Type) := {
  join_label: t -> Label -> t
}.
Notation "x ∪ y" := (join_label x y) (right associativity, at level 55).

Global Instance JoinLabel : Join Label := { join_label := join }.

Definition atom_join (a:Atom) (l':Label) : Atom :=
  match a with
    | Atm v l => Atm v (join l l')
  end.

Definition ptr_atom_join (pc:Ptr_atom) (l':Label) : Ptr_atom :=
  let '(PAtm i l) := pc in PAtm i (join_label l l').

Global Instance JoinAtom : Join Atom := { join_label := atom_join }.
Global Instance JoinPtrAtom : Join Ptr_atom := { join_label := ptr_atom_join }.

Ltac try_split_congruence :=
  try solve [left; congruence | right; congruence].

Definition mframe_eq (m1 m2 : mframe) : bool :=
  if Mem.EqDec_block m1 m2 then true else false.

Definition val_eq (v1 v2 : Value) : bool :=
  match v1, v2 with
    | Vint  i1, Vint i2  => Z_eq i1 i2
    | Vlab  l1, Vlab l2  => label_eq l1 l2
    | Vptr (Ptr mf1 i1), Vptr (Ptr mf2 i2) =>
      (mframe_eq mf1 mf2 && Z_eq i1 i2)%bool
    | _, _ => false
  end.

Definition val_eq_val (v1 v2 : Value) : Value :=
  Vint (if val_eq v1 v2 then 1 else 0).

(* CH: TODO: we should get rid of this crap! *)
(* Proof-stuff previously in Memory.v *)
Global Instance EqDec_block : EqDec Value eq.
Proof.
  intros x y;
  unfold complement, equiv; simpl;
  destruct x; destruct y; try_split_congruence.
  - destruct (Z.eq_dec n n0); subst; auto; try_split_congruence.
  - destruct p; destruct p0;
    destruct (Z.eq_dec i i0); destruct (fp == fp0);
    try_split_congruence.
  - destruct (LatEqDec Label l l0); try_split_congruence.
Qed.

Definition eval_binop (b : BinOpT) (v1 v2 : Value) : option Value :=
  match b, v1, v2 with
    | BAdd,     Vint z1, Vint z2 => Some (Vint (z1 + z2)%Z)
    | BMult,    Vint z1, Vint z2 => Some (Vint (z1 * z2)%Z)
    | BFlowsTo, Vlab l1, Vlab l2 => Some (Vint (flows_to l1 l2))
    | BJoin,    Vlab l1, Vlab l2 => Some (Vlab (l1 ∪ l2))
    | BEq,      v1     , v2      => Some (val_eq_val v1 v2)
    | _ ,       _ ,      _       => None
  end.

Definition memory := Mem.t Atom Label.
(* Specialize the Memory frame declaration *)
Definition frame := @frame Atom Label.

Definition alloc (size:Z) (lab stamp:Label) (a:Atom) (m:memory)
: option (mframe * memory) :=
  match zreplicate size a with
    | Some fr => Some (Mem.alloc Local m stamp (Fr stamp lab fr))
    | _ => None
  end.

Definition load (m : memory) (p : Pointer) : option Atom :=
  let '(Ptr f addr) := p in
  match Mem.get_frame m f with
    | None => None
    | Some (Fr _ _ fr) => nth_error_Z fr addr
  end.

Definition store (m : memory) (p : Pointer) (a:Atom)
: option (memory) :=
  let '(Ptr f addr) := p in
  match Mem.get_frame m f with
    | None => None
    | Some (Fr stamp lab data) =>
      match update_list_Z data addr a with
        | None => None
        | Some data' => (Mem.upd_frame m f (Fr stamp lab data'))
      end
  end.

Definition msize (m:memory) (p:Pointer) : option nat :=
  let (fp,i) := p in
  match Mem.get_frame m fp with
    | Some (Fr _ _ data) => Some (length data)
    | _ => None
  end.

Definition mlab (m:memory) (p:Pointer) : option Label :=
  let (fp,i) := p in
  match Mem.get_frame m fp with
    | Some (Fr _ l _) => Some l
    | _ => None
  end.

Lemma load_alloc : forall size stamp label a m m' mf,
    alloc size stamp label a m = Some (mf, m') ->
    forall mf' ofs',
      load m' (Ptr mf' ofs') =
        if mf == mf' then
          if Z_le_dec 0 ofs' then
            if Z_lt_dec ofs' size then Some a else None
          else None
        else load m (Ptr mf' ofs').
Proof.
  unfold alloc, load; intros.
  destruct (zreplicate size a) eqn:Ez; try congruence; inv H.
  rewrite (Mem.alloc_get_frame _ _ _ _ _ _ _ _ _ H1).
  destruct (equiv_dec mf).
  - inv e.
    destruct (equiv_dec mf'); try congruence.
    eapply nth_error_Z_zreplicate; eauto.
  - destruct (equiv_dec mf); try congruence.
Qed.

Lemma load_store : forall {m m'} {b ofs a},
    store m (Ptr b ofs) a = Some m' ->
    forall b' ofs',
      load m' (Ptr b' ofs') =
      if b == b' then
        if Z_eq_dec ofs ofs' then Some a else load m (Ptr b' ofs')
      else load m (Ptr b' ofs').
Proof.
  unfold store, load; intros.
  destruct (Mem.get_frame m b) eqn:E1; try congruence.
  destruct f as [stmp lab l].
  destruct (update_list_Z l ofs a) eqn:E2; try congruence.
  rewrite (Mem.get_upd_frame _ _ _ _ _ _ _ H).
  destruct (equiv_dec b);
  destruct (equiv_dec b); try congruence.
  - inv e; clear e0.
    destruct Z.eq_dec.
    + inv e.
      eapply update_list_Z_spec; eauto.
    + rewrite E1.
      symmetry.
      eapply update_list_Z_spec2; eauto.
Qed.

Lemma load_store_old : forall {m m':memory} {b ofs a},
    store m (Ptr b ofs) a = Some m' ->
    forall b' ofs',
      (b',ofs') <> (b,ofs) ->
      load m' (Ptr b' ofs') = load m (Ptr b' ofs').
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec mframe); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_store_new : forall {m m':memory} {b ofs a},
    store m (Ptr b ofs) a = Some m' ->
    load m' (Ptr b ofs) = Some a.
Proof.
  intros.
  rewrite (load_store H).
  destruct (@equiv_dec mframe); try congruence.
  destruct Z.eq_dec; try congruence.
Qed.

Lemma load_some_store_some : forall {m:memory} {b ofs a},
    load m (Ptr b ofs) = Some a ->
    forall a':Atom,
      exists m', store m (Ptr b ofs) a' = Some m'.
Proof.
  unfold load, store; intros.
  destruct (Mem.get_frame m b) eqn:E; try congruence.
  destruct f eqn:?. (* I don't like this *)
  exploit nth_error_Z_valid; eauto.
  destruct 1.
  destruct (@update_list_Z_Some _ a' l ofs); auto.
  rewrite H2.
  eapply Mem.upd_get_frame; eauto.
Qed.

Lemma alloc_get_frame_old :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (f f' : @Memory.frame T S) b b' mem'
         (ALLOC : Mem.alloc mode mem stamp f' = (b', mem'))
         (FRAME : Mem.get_frame mem b = Some f),
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b' == b) as [E | E]; auto.
  compute in E. subst b'.
  exploit Mem.alloc_get_fresh; eauto.
  congruence.
Qed.

Lemma alloc_get_frame_new :
  forall T S {eqS : EqDec S eq} mode mem (stamp : S) (frame : @Memory.frame T S) b mem'
         (ALLOC : Mem.alloc mode mem stamp frame = (b, mem')),
    Mem.get_frame mem' b = Some frame.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b) as [E | E]; auto.
  congruence.
Qed.

Lemma get_frame_upd_frame_eq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b f m'
         (UPD : Mem.upd_frame m b f = Some m'),
    Mem.get_frame m' b = Some f.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b); eauto.
  congruence.
Qed.

Lemma get_frame_upd_frame_neq :
  forall T S {eqS : EqDec S eq}
         (m : Mem.t T S) b b' f m'
         (UPD : Mem.upd_frame m b f = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  intros.
  erewrite Mem.get_upd_frame; eauto.
  destruct (equiv_dec b b'); congruence.
Qed.

Lemma get_frame_store_neq :
  forall (m : memory ) b b' off a m'
         (STORE : store m (Ptr b off) a = Some m')
         (NEQ : b' <> b),
    Mem.get_frame m' b' = Mem.get_frame m b'.
Proof.
  unfold store.
  intros.
  destruct (Mem.get_frame m b) as [f|] eqn:FRAME; try congruence.
  destruct f as [stamp lab l] eqn:?.
  destruct (update_list_Z l off a) as [l'|] eqn:NEWFRAME; try congruence.
  eapply get_frame_upd_frame_neq; eauto.
Qed.

Lemma alloc_get_frame_eq :
  forall m s (mem : memory) f b mem',
    Mem.alloc m mem s f = (b, mem') ->
    Mem.get_frame mem' b = Some f.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b); congruence.
Qed.

Lemma alloc_get_frame_neq :
  forall m s (mem : memory) f b b' mem',
    Mem.alloc m mem s f = (b, mem') ->
    b <> b' ->
    Mem.get_frame mem' b' = Mem.get_frame mem b'.
Proof.
  intros.
  erewrite Mem.alloc_get_frame; eauto.
  destruct (b == b'); congruence.
Qed.

Definition extends (m1 m2 : memory) : Prop :=
  forall b fr, Mem.get_frame m1 b = Some fr -> Mem.get_frame m2 b = Some fr.

Lemma extends_refl : forall (m : memory), extends m m.
Proof. unfold extends. auto. Qed.

Lemma extends_trans : forall (m1 m2 m3 : memory),
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof. unfold extends. auto. Qed.

Lemma extends_load (m1 m2 : memory) b off a :
  forall (EXT : extends m1 m2)
         (DEF : load m1 (Ptr b off) = Some a),
    load m2 (Ptr b off) = Some a.
Proof.
  intros.
  unfold load in *.
  destruct (Mem.get_frame m1 b) as [fr|] eqn:FRAME; inv DEF.
  erewrite EXT; eauto.
Qed.

(* Machine states *)

Record State := St {
  st_imem  : imem;    (* instruction memory *)
  st_mem   : memory;  (* data memory *)
  st_stack : Stack;   (* operand stack *)
  st_regs  : regSet;  (* register set *)
  st_pc    : Ptr_atom (* program counter *)
}.

Definition registerUpdate (rs : regSet) (r : regId) (a : Atom) :=
  update_list_Z rs r a.
Definition registerContent (rs : regSet) (r : regId) :=
  nth_error_Z rs r.

Definition run_tmr (t : table) (op: OpCode)
  (labs:Vector.t Label (labelCount op)) (pc: Label)
   : option (option Label * Label) :=
  let r := t op in
  apply_rule r labs pc.

(** Declarative semantics *)

Local Open Scope Z_scope.
(* CH: we only need to instantiate this for the default table,
       so we could even consider baking it in *)
Inductive step (t : table) : State -> State -> Prop :=
 | step_lab: forall im μ σ v K pc r r' r1 r2 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Lab r1 r2))
     (REG1: registerContent r r1 = Some (v @ K))
     (TMU: run_tmr t OpLab <||> LPC = Some (Some rl, rpcl))
     (UPD: registerUpdate r r2 (Vlab K @ rl) = Some r'),
     step t
          (St im μ σ r pc)
          (St im μ σ r' (PAtm (j+1) rpcl))
 | step_pclab: forall im μ σ pc r r' r1 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (PcLab r1))
     (TMU: run_tmr t OpPcLab <||> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r1 (Vlab (∂ pc) @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_mlab: forall im μ σ pc r r1 r2 p K C j LPC rl r' rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (MLab r1 r2))
     (OLD : mlab μ p = Some C)
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (TMU : run_tmr t OpMLab <|K; C|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (Vlab C @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (Zsucc j) rpcl))
 | step_putlab: forall im μ σ pc r r' r1 j LPC rl rpcl l
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (PutLab l r1))
     (TMU : run_tmr t OpPutLab <||> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r1 (Vlab l @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_bcall: forall im μ σ pc B K r r1 r2 r3 j La addr Lpc rl rpcl
     (PC: pc = PAtm j Lpc)
     (CODE: im[pc] = Some (BCall r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vint addr @ La))
     (OP2 : registerContent r r2 = Some (Vlab B @ K))
     (TMU : run_tmr t OpBCall <|La; K|> Lpc = Some (Some rl, rpcl)),
     step t
       (St im μ σ r pc)
       (St im μ (ST (SF (PAtm (j+1) rl) r r3 B :: (unStack σ))) r (PAtm addr rpcl))
 | step_bret: forall im μ σ pc a r r' r'' r1 R pc' B j j' LPC LPC' rl rpcl
     (PC: pc  = PAtm j  LPC)
     (PC': pc' = PAtm j' LPC')
     (CODE: im[pc] = Some BRet)
     (STAYS : registerContent r r1 = Some (a @ R))
     (TMU : run_tmr t OpBRet <|R; B; LPC'|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r' r1 (a @ rl) = Some r''),
     step t
       (St im μ (ST (SF pc' r' r1 B :: (unStack σ))) r pc)
       (St im μ σ r'' (PAtm j' rpcl))
 | step_alloc: forall im μ μ' σ pc r r' r1 r2 r3 i K Ll K' rl rpcl j LPC dfp
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Alloc r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vint i @ K))
     (OP2 : registerContent r r2 = Some (Vlab Ll @ K'))
     (TMU : run_tmr t OpAlloc <|K; K'; Ll|> LPC = Some (Some rl, rpcl))
     (ALLOC: alloc i Ll (K ∪ K' ∪ LPC) (Vint 0 @ ⊥) μ = Some (dfp, μ'))
     (* LL: Using label Ll directly as the label of the mframe,
        also using rl for both the pointer label and the stamp *)
     (RES : registerUpdate r r3 (Vptr (Ptr dfp 0) @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ' σ r' (PAtm (j+1) rpcl))
 | step_load: forall im μ σ pc C p K r r' r1 r2 j LPC v Ll rl rpcl
     (PC  : pc = PAtm j LPC)
     (CODE: im[pc] = Some (Load r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (READ: load μ p = Some (v @ Ll))
     (MLAB: mlab μ p = Some C)
     (TMU : run_tmr t OpLoad <|K; C; Ll|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (v @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_store: forall im μ σ pc v p μ' r r1 r2 j LPC rpcl rl lp lf lv
     (PC  : pc = PAtm j LPC)
     (CODE: im[pc] = Some (Store r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr p @ lp))
     (OP2 : registerContent r r2 = Some (v @ lv))
     (MLAB: mlab μ p = Some lf)
     (TMU : run_tmr t OpStore <|lp; lf; lv|> LPC = Some (Some rl, rpcl))
     (WRITE: store μ p (v @ rl) = Some μ'),
     step t
       (St im μ σ r pc)
       (St im μ' σ r (PAtm (j+1) rpcl))
 | step_write: forall im μ σ pc v p μ' r r1 r2 j LPC rpcl rl v' lp lv lv' lf
     (PC  : pc = PAtm j LPC)
     (CODE: im[pc] = Some (Store r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr p @ lp))
     (OP2 : registerContent r r2 = Some (v @ lv))
     (READ: load μ p = Some (v' @ lv'))
     (MLAB: mlab μ p = Some lf)
     (TMU : run_tmr t OpWrite <|lp;lf;lv;lv'|> LPC = Some (Some rl, rpcl))
     (WRITE: store μ p (v @ rl) = Some μ'),
     step t
       (St im μ σ r pc)
       (St im μ' σ r (PAtm (j+1) rpcl))
 | step_jump: forall im μ σ pc addr Ll r r1 j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Jump r1))
     (OP1 : registerContent r r1 = Some (Vint addr @ Ll))
     (TMU: run_tmr t OpJump <|Ll|> LPC = Some (None, rpcl)),
     step t
       (St im μ σ r pc)
       (St im μ σ r (PAtm addr rpcl))
 | step_bnz_yes: forall im μ σ pc n m K r r1 j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (BNZ n r1))
     (OP1 : registerContent r r1 = Some (Vint m @ K))
     (TMU: run_tmr t OpBNZ <|K|> LPC = Some (None, rpcl))
     (TEST: m <> 0),
     step t
       (St im μ σ r pc)
       (St im μ σ r (PAtm (j + n) rpcl))
 | step_bnz_no: forall im μ σ pc n m K r r1 j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (BNZ n r1))
     (OP1 : registerContent r r1 = Some (Vint m @ K))
     (TMU: run_tmr t OpBNZ <|K|> LPC = Some (None, rpcl))
     (TEST: m = 0),
     step t
       (St im μ σ r pc)
       (St im μ σ r (PAtm (j + 1) rpcl))
 | step_psetoff: forall im μ σ pc fp' j K1 n K2 r r' r1 r2 r3 j' LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (PSetOff r1 r2 r3))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp' j') @ K1))
     (OP2 : registerContent r r2 = Some (Vint n @ K2))
     (TMU: run_tmr t OpPSetOff <|K1; K2|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r3 (Vptr (Ptr fp' n) @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j + 1) rpcl))
 | step_put: forall im μ σ pc x r r' r1 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Put x r1))
     (TMU : run_tmr t OpPut <||> LPC = Some (Some rl, rpcl))
     (OP1 : registerUpdate r r1 (Vint x @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_binop: forall im μ σ pc o v1 L1 v2 L2 v r r1 r2 r3 r' j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (BinOp o r1 r2 r3))
     (OP1 : registerContent r r1 = Some (v1 @ L1))
     (OP2 : registerContent r r2 = Some (v2 @ L2))
     (TMU : run_tmr t OpBinOp <|L1; L2|> LPC = Some (Some rl, rpcl))
     (BINOP: eval_binop o v1 v2 = Some v)
     (RES : registerUpdate r r3 (v @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_nop: forall im μ σ pc r j LPC rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some Nop)
     (TMU : run_tmr t OpNop <||> LPC = Some (None, rpcl)),
     step t
       (St im μ σ r pc)
       (St im μ σ r (PAtm (j+1) rpcl))
 | step_msize: forall im μ σ pc p K C r r' r1 r2 j LPC rl rpcl n
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (MSize r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr p @ K))
     (MLAB: mlab μ p = Some C)
     (TMU: run_tmr t OpMSize <|K; C|> LPC = Some (Some rl, rpcl))
     (MSIZE: msize μ p = Some n)
     (RES : registerUpdate r r2 (Vint (Z.of_nat n) @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_pgetoff: forall im μ σ pc fp' j K r r' r1 r2 j' LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (PGetOff r1 r2))
     (OP1 : registerContent r r1 = Some (Vptr (Ptr fp' j') @ K))
     (TMU: run_tmr t OpPGetOff <|K|> LPC = Some (Some rl, rpcl))
     (RES : registerUpdate r r2 (Vint j' @ rl) = Some r'),
     step t
       (St im μ σ r pc)
       (St im μ σ r' (PAtm (j+1) rpcl))
 | step_mov: forall im μ σ v K pc r r' r1 r2 j LPC rl rpcl
     (PC: pc = PAtm j LPC)
     (CODE: im[pc] = Some (Mov r1 r2))
     (REG1: registerContent r r1 = Some (v @ K))
     (TMU: run_tmr t OpMov <|K|> LPC = Some (Some rl, rpcl))
     (UPD: registerUpdate r r2 (v @ rl) = Some r'),
     step t
          (St im μ σ r pc)
          (St im μ σ r' (PAtm (j+1) rpcl)).

(** * Executable semantics *)

Definition state_instr_lookup (st:State) : option (@Instr Label) :=
  let (im,_,_,_,pc) := st in im[pc].

Definition fstep t (st:State) : option State :=
  do instr <- state_instr_lookup st;
  let '(St im μ σ r pc) := st in
  let '(PAtm j LPC) := pc in
  match instr with
    | Lab r1 r2 =>
      match registerContent r r1 with
        | Some (_ @ K) =>
          match run_tmr t OpLab <||> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r2 (Vlab K @ rl);
                Some (St im μ σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | None => None
      end
    | PcLab r1 =>
      match run_tmr t OpPcLab <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vlab (∂ pc) @ rl);
            Some (St im μ σ r' (PAtm (j+1) rpcl))
        | _ => None
      end
    | MLab r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do C <- mlab μ p;
            match run_tmr t OpMLab <|K; C|> LPC with
              | Some (Some rl, rpcl) =>
                do r' <- registerUpdate r r2 (Vlab C @ rl);
                Some (St im μ σ r' (PAtm (j+1) rpcl))
              | _ => None
            end
        | _ => None
      end
    | PutLab l r1 =>
      match run_tmr t OpPutLab <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vlab l @ rl);
          Some (St im μ σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
    | BCall r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vint addr @ Ll), Some (Vlab B @ K) =>
          match run_tmr t OpBCall <|Ll; K|> LPC with
            | Some (Some rl, rpcl) =>
              Some (St im μ (ST (SF (PAtm (j+1) rl) r r3 B :: (unStack σ))) r
                       (PAtm addr rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | BRet =>
      match unStack σ with
        | SF (PAtm jp' LPC') savedRegs r1 B :: σ' =>
          do r1Cont <- registerContent r r1;
          let '(a @ R) := r1Cont in
          match run_tmr t OpBRet <|R; B; LPC'|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate savedRegs r1 (a @ rl);
              Some (St im μ (ST σ') r' (PAtm jp' rpcl))
            | _ => None
          end
        | _ => None
      end
    | Alloc r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vint i @ K), Some (Vlab Ll @ K') =>
          match run_tmr t OpAlloc <|K; K'; Ll|> LPC with
            | Some (Some rl, rpcl) =>
              let stmp := K ∪ K' ∪ LPC in
                 (* this stamp is just instrumentation;
                    and it doesn't go via the rule table *)
              do alloc_res : (mframe * memory) <- alloc i Ll stmp (Vint 0 @ ⊥) μ;
              let (dfp, μ') := alloc_res in
              do r' <- registerUpdate r r3 (Vptr (Ptr dfp 0) @ rl);
              Some (St im μ' σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Load r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do a <- load μ p;
            let '(v @ Ll) := a in
            do C <- mlab μ p;
            match run_tmr t OpLoad <|K; C; Ll|> LPC with
              | Some (Some rl (* Ll *), rpcl (* LPC ∪ K ∪ C *)) =>
                do r' <- registerUpdate r r2 (v @ rl);
                Some (St im μ σ r' (PAtm (j+1) (rpcl)))
              | _ => None
            end
        | _ => None
      end
    | Store r1 r2 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vptr p @ lp), Some (v @ lv) =>
          do lf <- mlab μ p;
          match run_tmr t OpStore <|lp; lf; lv|> LPC with
            (* check: lp ∪ LPC <: lf *)
            | Some (Some rl (* lv *), rpcl (* LPC *)) =>
              do μ' <- store μ p (v @ rl);
              Some (St im μ' σ r (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Write r1 r2 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vptr p @ lp), Some (v @ lv) =>
          do a <- load μ p;
          let '(_ @ lv') := a in
          do lf <- mlab μ p;
          match run_tmr t OpWrite <|lp; lf; lv; lv'|> LPC with
            | Some (Some rl, rpcl) =>
              do μ' <- store μ p (v @ rl);
              Some (St im μ' σ r (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Jump r1 =>
      match registerContent r r1 with
        | Some (Vint addr @ Ll) =>
          match run_tmr t OpJump <|Ll|> LPC with
            | Some (None, rpcl) =>
              Some (St im μ σ r (PAtm addr rpcl))
            | _ => None
          end
        | _ => None
      end
    | BNZ n r1 =>
      match registerContent r r1 with
        | Some (Vint m @ K) =>
          match run_tmr t OpBNZ <|K|> LPC with
            | Some (None, rpcl) =>
              let new_pc := (if Z_eq_dec m 0 then j+1 else j+n) in
                Some (St im μ σ r (PAtm new_pc rpcl))
            | _ => None
          end
        | _ => None
      end
    | PSetOff r1 r2 r3 =>
      match registerContent r r1, registerContent r r2 with
        | Some (Vptr (Ptr fp' j') @ K1), Some (Vint n @ K2) =>
          match run_tmr t OpPSetOff <|K1; K2|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r3 (Vptr (Ptr fp' n) @ rl);
              Some (    St im μ σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _, _ => None
      end
    | Put x r1 =>
      match run_tmr t OpPut <||> LPC with
        | Some (Some rl, rpcl) =>
          do r' <- registerUpdate r r1 (Vint x @ rl);
            Some (St im μ σ r' (PAtm (j+1) rpcl))
        | _ => None
      end
     | BinOp o r1 r2 r3 =>
       match registerContent r r1, registerContent r r2 with
         | Some (v1 @ L1), Some (v2 @ L2) =>
           match run_tmr t OpBinOp <|L1; L2|> LPC with
             | Some (Some rl, rpcl) =>
               do v <- eval_binop o v1 v2;
               do r' <- registerUpdate r r3 (v @ rl);
               Some (St im μ σ r' (PAtm (j+1) rpcl))
             | _ => None
           end
         | _, _ => None
       end
     | Nop =>
       match run_tmr t OpNop <||> LPC with
         | Some (None, rpcl) =>
           Some (St im μ σ r (PAtm (j+1) rpcl))
         | _ => None
       end
    | MSize r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr p @ K) =>
            do C <- mlab μ p;
            match run_tmr t OpMSize <|K; C|> LPC with
              | Some (Some rl, rpcl) =>
                do n <- msize μ p;
                do r' <- registerUpdate r r2 (Vint (Z.of_nat n) @ rl);
                Some (St im μ σ r' (PAtm (j+1) rpcl))
              | _ => None
            end
        | _ => None
      end
    | PGetOff r1 r2 =>
      match registerContent r r1 with
        | Some (Vptr (Ptr fp' j') @ K) =>
          match run_tmr t OpPGetOff <|K|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r2 (Vint j' @ rl);
              Some (St im μ σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | _ => None
      end
    | Mov r1 r2 =>
      match registerContent r r1 with
        | Some (v @ K) =>
          match run_tmr t OpMov <|K|> LPC with
            | Some (Some rl, rpcl) =>
              do r' <- registerUpdate r r2 (v @ rl);
                Some (St im μ σ r' (PAtm (j+1) rpcl))
            | _ => None
          end
        | None => None
      end
    | Halt => None
  end.

Lemma fstepP t st st' : fstep t st = Some st' -> step t st st'.
Proof.
admit.
Qed.


Ltac fstep_solver :=
  repeat (simpl; match goal with
            | |- context[registerContent ?rs ?reg] =>
              remember (registerContent rs reg) as Hyp; destruct Hyp
            | |- context[do _ <- Some ?x; _] =>
              case_eq x; [simpl; intro; intro|simpl; congruence]
            | |- context[do _ <- ?x; _] =>
              case_eq x; [simpl; intro; intro|simpl; congruence]
            | |- context[match ?s with | (_,_) => _ end] =>
              case_eq s; intro; intro; intro
            | |- context[match ?s with | _ => _ end] =>
              destruct s
            | |- context[match ?s with | Some _ => _ | None => _ end] =>
              destruct s
(*            | |- context[Atm (Vptr (Ptr ?fp ?i)) ?l] =>
              replace (Vptr (Ptr fp i) @ l)
              with (ptr_atom_to_atom (PAtm i l)) by auto
*)
            | |- Some _ = None -> _ => intros contra; inversion contra
            | |- None = Some _ -> _ => intros contra; inversion contra
          end); try congruence;
  try match goal with
    | |- Some _ = Some _ -> _ =>
      intros T; inversion T; clear T; subst; try (econstructor (solve[eauto]))
  end.

(* TODO: bring back the equivalence proof
Hint Unfold run_tmr.
Hint Unfold apply_rule.
Hint Unfold default_table.
Hint Resolve Ptr_atom_inhabited.
Theorem fstep_make_a_step : forall t st1 st2 tr,
  fstep t st1 = Some (tr, st2) ->
  step t st1 tr st2.
Proof.
  destruct st1 as (μ,π,σ,regs,pc).
  unfold fstep; simpl.
  case_eq (μ[pc]); simpl bind; [|simpl bind; congruence].
  intros ins Hins.
  intros st2 tr.
  destruct ins;
  fstep_solver;
  try solve [econstructor; eauto; auto].
Admitted.
(*
  (* TODO: Figure out how to choose the correct econstructor *)
  eapply step_memlab; eauto; auto.
  eapply step_pclab; eauto; auto.
  eapply step_bret; eauto; auto. admit. (* FIX RET! *)
  eapply step_flowsto; eauto; auto.
  eapply step_ljoin; eauto; auto.
  eapply step_pushbot; eauto; auto.
    instantiate (1 := l); auto.
  eapply step_push; eauto; auto.
  eapply step_binop; eauto; auto.
  eapply step_jump; eauto; auto. admit.
  eapply step_load; eauto; auto.
  eapply step_store; eauto; auto. admit. (* WHY!? *)
  eapply step_alloc; eauto; auto. admit.
  eapply step_psetoff; eauto; auto.
Qed.
*)
*)
Fixpoint fstepN t (n : nat) (s : State) : list State :=
  match n with
    | O => (s :: nil)
    | S n' =>
      match fstep t s with
        | Some s' =>
          let res := fstepN t n' s' in
          (s :: res)
        | None => (s :: nil)
      end
  end%list.

End MachineM.