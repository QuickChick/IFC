Require Import Coq.Strings.String.
Require Import Arith.EqNat.
Require Import ZArith.

From QuickChick Require Import QuickChick.

Require Import Machine.
Require Import TestingCommon.
Require Import Printing.
Require Import Shrinking.
Require Import Generation.

Open Scope string_scope.

Require Import Reachability.

Definition is_low_state st lab := isLow (pc_lab (st_pc st)) lab.

Record exp_result := MkExpResult { exp_success : Checker
                                 ; exp_fail    : Checker
                                 ; exp_reject  : Checker
                                 ; exp_check   : bool -> Checker
                                 }.

(* HACK: To get statistics on successful runs/discards/avg test failures, we can 
   assume everything succeeds and collect the result. *)
Definition exp_result_random : exp_result :=
  {| exp_success := collect true  true
   ; exp_fail    := collect false true
   ; exp_reject  := collect "()"  true
   ; exp_check   := (fun b => collect b true)
  |}.

(* For fuzzing, we let afl-fuzz gather the statistics (and hack afl-fuzz instead :) *)
Definition exp_result_fuzz : exp_result :=
  {| exp_success := collect true  true
   ; exp_fail    := collect false false
   ; exp_reject  := collect "()"  tt
   ; exp_check   := (fun b => collect b b)
  |}.

Definition propSSNI_helper (t : table) (v : Variation) (res : exp_result) : Checker  :=
    let '(Var lab st1 st2) := v in
    if indist lab st1 st2 then
      (* XXX Our generator should always give us this by design.
         If that's not the case the generator is broken. *)
      match fstep t st1  with
      | Some st1' =>
        if is_low_state st1 lab then
          match fstep t st2 with
          | Some st2' =>
             exp_check res (indist lab st1' st2')
          | _ => exp_reject res
          (* XXX This used to fail the checker in ICFP paper.
             But here it does happen for Alloc, Store and BRet *)
          end
        else (* is_high st1 *)
          if is_low_state st1' lab then
            match fstep t st2 with
            | Some st2' =>
              if is_low_state st2' lab then
                exp_check res (indist lab st1' st2') 
              else exp_success res
            | _ => exp_success res
            end
          else
            exp_check res (indist lab st1 st1')
      | _ => exp_success res
      end
    else exp_reject res.

  Definition propSSNI_smart r t : Checker :=
    forAllShrinkShow gen_variation_state (fun _ => nil) (fun _ => ""%string)
      (* shrinkVState *)
      (fun v => propSSNI_helper t v r).

  Definition propSSNI_enum r t : Checker :=
    forAllShrinkShow gen_variation_state_enum (fun _ => nil) (fun _ => ""%string)
      (* shrinkVState *)
      (fun v => propSSNI_helper t v r).

  Definition propSSNI_arb r t : Checker :=
    forAllShrinkShow arbitrary (fun _ => nil) (fun _ => ""%string)
      (fun v => propSSNI_helper t v r).

                     