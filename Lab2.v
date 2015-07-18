Require Import Labels.
Require Import ssreflect ssrbool ssrfun eqtype seq.

(** The two point finite lattice *)
Inductive Lab2 : Set :=
  | L : Lab2
  | H : Lab2.

Instance JoinSemiLattice_Lab2 : JoinSemiLattice Lab2 :=
{  bot := L
;  join l1 l2 :=
     match l1, l2 with
       | H, _ => H
       | _, H => H
       | L, L => L
     end
; flows l1 l2 :=
    match l1, l2 with
      | L, _ => true
      | _, H => true
      | _, _ => false
    end
; meet l1 l2 :=
    match l1, l2 with
    | L, _ => L
    | _, L => L
    | H, H => H
    end
}.
Proof.
auto.
intros l; destruct l; auto.
intros l1 l2 l3; destruct l1, l2, l3; auto.
intros l1 l2; destruct l1, l2; auto.
by [].
by [].
intros l1 l2; destruct l1, l2; auto.
intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.

Instance Lattice_Lab2 : Lattice Lab2 := { top := H }.
Proof. intros l; destruct l; auto. Defined.

Instance FiniteLattice_Lab2 : FiniteLattice Lab2 := { elems := [:: L;H] }.
Proof. by case. Defined.
