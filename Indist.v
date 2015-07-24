Require Import ZArith.
Require Import Instructions.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Require Import Utils Labels Memory Machine.
(*Require Import Common.*)

Module IndistM (Lattice : FINLAT).

Module GenericMachine := MachineM Lattice.

Import LabelEqType.

(* CH: things fail in very strange ways if this is just Import *)
Export GenericMachine.

Open Scope bool.

(* Indistinguishability type class *)
Class Indist (A : Type) : Type := {
  indist : Label -> A -> A -> bool;

  indistxx : forall obs, reflexive (indist obs);
  indist_sym : forall obs, symmetric (indist obs)
}.

Arguments indistxx {_ _} [obs] _.
Arguments indist_sym {_ _} [obs] _ _.

Instance oindist {T : Type} `{Indist T} : Indist (option T) := {

  indist obs x1 x2 :=
    match x1, x2 with
    | None, None => true
    | Some x1, Some x2 => indist obs x1 x2
    | _, _ => false
    end

}.

Proof.
- abstract by move => obs [x|//=]; rewrite indistxx.
- abstract by move => obs [x|//=] [y|//=]; rewrite indist_sym.
Defined.

Instance indistList {A : Type} `{Indist A} : Indist (list A) :=
{|
  indist lab l1 l2 :=
    (size l1 == size l2) && all (fun p => indist lab p.1 p.2) (zip l1 l2)
|}.

Proof.
- abstract by move => obs; elim => [|x l IH] //=; rewrite indistxx IH.
- abstract by move => obs; elim => [|x1 l1 IH] [|x2 l2] //=;
  rewrite !eqSS !(andbC (indist _ _ _)) !andbA IH indist_sym.
Defined.

Lemma indist_cons {A} `{Indist A} obs x1 l1 x2 l2 :
  indist obs (x1 :: l1) (x2 :: l2) =
  indist obs x1 x2 && indist obs l1 l2.
Proof. by rewrite {1 3}/indist /= eqSS; bool_congr. Qed.

(* Indistinguishability of Values.
   - Ignores the label (called only on unlabeled things)
   - Just syntactic equality thanks to the per-stamp-level allocator!
*)
Instance indistValue : Indist Value :=
{|
  indist _lab v1 v2 := v1 == v2
|}.

Proof.
- abstract by move => _; exact: eqxx.
- abstract by move=> _; exact: eq_sym.
Defined.

(* Indistinguishability of Atoms.
   - The labels have to be equal (observable labels)
   - If the labels are equal then:
     * If they are both less than the observability level then
       the values must be indistinguishable
     * Else if they are not lower, the label equality suffices
*)
Instance indistAtom : Indist Atom :=
{|
  indist lab a1 a2 :=
    let '(Atm v1 l1) := a1 in
    let '(Atm v2 l2) := a2 in
    (l1 == l2)
    && (isHigh l1 lab || indist lab v1 v2)
|}.

Proof.
- abstract by move => obs [v l]; rewrite eqxx indistxx orbT.
- abstract by move=> obs [v1 l1] [v2 l2]; rewrite eq_sym indist_sym;
  case: eqP=> [->|] //=.
Defined.

Instance indistFrame : Indist frame :=
{|
  indist lab f1 f2 :=
    let '(Fr l1 vs1) := f1 in
    let '(Fr l2 vs2) := f2 in
    (* CH: this part is basically the same as indistinguishability of values;
           try to remove this duplication at some point *)
    (l1 == l2) && (isHigh l1 lab || indist lab vs1 vs2)
|}.

Proof.
- abstract by move => obs [l vs]; rewrite !eqxx indistxx orbT /=.
- abstract by move=> obs [v1 l1] [v2 l2]; rewrite eq_sym indist_sym;
  case: eqP=> [->|] //=.
Defined.

(* Indistinguishability of memories
   - Get all corresponding memory frames
   - Make sure they are indistinguishable
   - Get all pairs that have been allocated in low contexts.
*)

Definition blocks_stamped_below (lab : Label) (m : memory) : seq mframe :=
  Mem.get_blocks (allThingsBelow lab) m.

Definition indistMemAsym lab m1 m2 :=
  all (fun b =>
         indist lab (Mem.get_frame m1 b) (Mem.get_frame m2 b))
      (blocks_stamped_below lab m1).

Instance indistMem : Indist memory :=
{|
  indist lab m1 m2 :=
    indistMemAsym lab m1 m2 && indistMemAsym lab m2 m1
|}.

Proof.
- abstract by move=> obs m; rewrite andbb /indistMemAsym;
  apply/allP=> b b_in; rewrite indistxx.
- abstract by move=> obs m1 m2; rewrite andbC.
Defined.

(* Indistinguishability of stack frames (pointwise)
     * The returning pc's must be equal
     * The saved registers must be indistinguishable
     * The returning register must be the same
     * The returning labels must be equal
*)

Instance indistStackFrame : Indist StackFrame :=
{|
  indist lab sf1 sf2 :=
    match sf1, sf2 with
      | SF p1 regs1 r1 l1, SF p2 regs2 r2 l2 =>
        (isLow (pc_lab p1) lab || isLow (pc_lab p2) lab) ==>
        [&& p1 == p2,
            indist lab regs1 regs2,
            r1 == r2 :> Z & l1 == l2]
    end
|}.
Proof.
- abstract by move=> obs [ra rs rr rl]; rewrite !eqxx indistxx /= implybT.
- abstract by move=> obs [ra1 rs1 rr1 rl1] [ra2 rs2 rr2 rl2];
  rewrite orbC (eq_sym ra1) indist_sym (eq_sym rr1) (eq_sym rl1).
Defined.

Definition stackFrameBelow (lab : Label) (sf : StackFrame) : bool :=
  let 'SF ret_addr  _ _ _ := sf in
  let 'PAtm _ l_ret_addr := ret_addr in
  flows l_ret_addr lab.

Instance indistStack : Indist Stack :=
{|
  indist lab s1 s2 :=
    indist lab (unStack s1) (unStack s2)
|}.
Proof.
- abstract by move=> obs s; rewrite indistxx.
- abstract by move=> obs s1 s2; exact: indist_sym.
Defined.

Instance indistImems : Indist imem :=
{|
  indist _lab imem1 imem2 := imem1 == imem2 :> seq (@Instr Label)
|}.

Proof.
- abstract by move => _ r; exact: eqxx.
- abstract by move => _ ??; exact: eq_sym.
Defined.

Instance indistState : Indist State :=
{|
  indist lab st1 st2 :=
    [&& indist lab (st_imem st1) (st_imem st2),
        indist lab (st_mem st1) (st_mem st2) &
        if isLow ∂(st_pc st1) lab || isLow ∂(st_pc st2) lab then
          [&& st_pc st1 == st_pc st2,
              indist lab (st_stack st1) (st_stack st2)
              & indist lab (st_regs st1) (st_regs st2)]
        else
          let lowsf sf :=
            let: SF (PAtm _ lab') _ _ _ := sf in flows lab' lab in
          let cropTop st := drop (find lowsf st) st in
          indist lab (cropTop (unStack (st_stack st1)))
                     (cropTop (unStack (st_stack st2))) ]
|}.

Proof.
- abstract by move => obs [imem m stk regs [v l]]; rewrite !indistxx eqxx /=; case: ifP.
- abstract by rewrite (lock (@indist));
  move=> obs [im1 m1 st1 rs1 [v1 l1]] [im2 m2 st2 rs2 [v2 l2]] /=;
  rewrite -!lock (indist_sym im1) (indist_sym m1) orbC (eq_sym)
          (indist_sym st1) (indist_sym rs1) (indist_sym (drop _ _)).
Defined.

End IndistM.
