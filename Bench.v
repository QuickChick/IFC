
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
Definition rSSNI_enum  := propSSNI_enum  exp_result_random. 

Extract Constant defNumTests => "1000000".

