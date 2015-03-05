Require Import List. Import ListNotations.
Require Import ZArith.
Require Import String.
Require Import NPeano.

Require Import QuickChick.
Import GenLow GenHigh.

Require Export Utils.
Require Export Labels.
Require Export Instructions.
Require Export Memory.
Require Export Lab4.
Require Export Indist.
Require Export Machine.

Module Lab4M <: FINLAT.
  Definition Label := Lab4.
  Definition FLat  := FiniteLattice_Lab4.
End Lab4M.

Module MachineLab4M := MachineM Lab4M.
Export MachineLab4M.

Module IndistLab4M := IndistM Lab4M.
Export IndistLab4M.



Definition pure {A : Type} (x : A) : G A := returnGen x.

(*
Fixpoint foldGen {A B : Type} (f : A -> B -> G A) (l : list B) (a : A)
: G A :=
  match l with
    | [] => returnGen a
    | (x :: xs) => bindGen (f a x) (foldGen f xs)
  end.
*)

(* Variation stuff - should be deleted -- CH: ha? it seems used *)
Inductive Variation {A : Type} :=
| Var : Lab4 -> A -> A -> Variation.

Class ShrinkV (A : Type) := { shrinkV : @Variation A -> list (@Variation A) }.
(* End of to be deleted *)

Definition validJump (st : State) (addr : Z) :=
  let '(St imem _ _ _ _) := st in
  (Z.to_nat addr) <? (List.length imem).
