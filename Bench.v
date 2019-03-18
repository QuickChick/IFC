
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import List. Import ListNotations.

Set Warnings "-extraction-reserved-identifier".

From QuickChick Require Import QuickChick.

Require Import IFC.Rules.
Require Import IFC.TestingCommon.
Require Import IFC.Generation.
Require Import IFC.Shrinking.
Require Import IFC.SSNI.
Require Import IFC.Reachability.
Require Import IFC.SingleStateArb.

Require Import IFC.SanityChecks.

Require Import Mutate.

Definition testMutantX_ p n : Checker :=
  p (nth n (mutate_table default_table) default_table).

Definition rSSNI_smart := propSSNI_smart exp_result_random.
Definition fSSNI_smart := propSSNI_smart exp_result_fuzz.
Definition rSSNI_naive := propSSNI_arb   exp_result_random.
Definition fSSNI_naive := propSSNI_arb   exp_result_fuzz.

Definition nth_table n := nth n (mutate_table default_table) default_table.

Definition qcfSSNI_copy_prop_0 :=
  fun v => propSSNI_helper (nth_table 0) v exp_result_opt_bool.

Definition qcfSSNI_copy_loop_0 :=
  fun (_ : unit) => fuzzLoop gen_variation_copy fuzz show qcfSSNI_copy_prop_0.

Definition prop :=
  forAll (bindGen (resize 2 gen_variation_copy) fuzz) (fun v =>
  match qcfSSNI_copy_prop_0 v with
  | Some b => checker b
  | None => checker tt
  end).

(*
QuickChick prop.

Sample (bindGen (resize 2 gen_variation_copy) fuzz).
*)
ManualExtract [BinOpT; Label; Instr; Pointer; Value; Atom; Ptr_atom; StackFrame; Stack; memframe; State; Variation].

Extract Constant defNumTests => "100000".
FuzzQC qcfSSNI_copy_prop_0 (qcfSSNI_copy_loop_0 tt).
(*
QuickChick (testMutantX_ rSSNI_naive 0).
FuzzChick (testMutantX_ 0).
*)
