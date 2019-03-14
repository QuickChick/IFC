From QuickChick Require Import QuickChick.

Require Import Machine.

Require Import ZArith.
Require Import List.

Require Import TestingCommon.
Require Import Indist.
Require Import Generation.
Require Import Shrinking.
Require Import Printing.

(* Leverage the pair/V functions and making everything observable,
   create (inefficient) instances for a single machine *)

(* Generates an SSNI-oriented single machine state *)
Definition genState : G State :=
  bindGen gen_variation_state (fun v =>
  let '(Var _ st _) := v in
  returnGen st).

Instance gState : Gen State :=
{|
  arbitrary := @genState 
|}.

Instance shrState : Shrink State :=
{| shrink x :=
    let all : list (@Variation State):= shrinkVState (Var top x x) in
    let state_of_var v := let '(Var _ x _) := v in x in
    filter (indist top x) (List.map state_of_var all)
|}.

Instance showState : Show State :=
{|
  show x := show_pair top x x
|}.
