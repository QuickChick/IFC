Require Import Labels.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.

(** The four point finite lattice (diamond shape) *)
Inductive Lab4 : Set :=
  | L  : Lab4
  | M1 : Lab4
  | M2 : Lab4
  | H  : Lab4.

Instance JoinSemiLattice_Lab4 : JoinSemiLattice Lab4 :=
{  bot := L
;  join l1 l2 :=
     match l1, l2 with
       | _ , H  => H
       | H , _  => H
       | L , _  => l2
       | _ , L  => l1
       | M1, M2 => H
       | M2, M1 => H
       | _ , _  => l1 (* l1 == l2 *)
     end
; flows l1 l2 :=
    match l1, l2 with
      | L , L  => true
      | L , M1 => true
      | L , M2 => true
      | L , H  => true
      | M1, M1 => true
      | M1, H  => true
      | M2, M2 => true
      | M2, H  => true
      | H , H  => true
      | _ , _  => false
    end
; meet l1 l2 :=
     match l1, l2 with
       | _ , L  => L
       | L , _  => L
       | H , _  => l2
       | _ , H  => l1
       | M1, M2 => L
       | M2, M1 => L
       | _ , _  => l1 (* l1 == l2 *)
     end
}.
Proof.
now intros l; destruct l; auto.
now intros l; destruct l; auto.
now intros l1 l2 l3; destruct l1, l2, l3; auto.
now intros l1 l2; destruct l1, l2; auto.
now intros l1 l2; destruct l1, l2; auto.
now intros l1 l2; destruct l1, l2; auto.
intros l1 l2 l; destruct l1, l2, l; auto.
Defined.

Instance Lattice_Lab4 : Lattice Lab4 := { top := H }.
Proof. intros l; destruct l; auto. Defined.

Instance FiniteLattice_Lab4 : FiniteLattice Lab4 := { all_labels := [:: L;M1;M2;H] }.
Proof. by case. Defined.
