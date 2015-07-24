Require Import QuickChick.
Import GenLow GenHigh.

Require Import Reachability.
Require Import Printing.
Require Import SingleStateArb.
Require Import Indist.
Require Import Shrinking.
Require Import Generation.
Require Import Machine.

Require Import List. Import ListNotations.
Require Import TestingCommon.
Require Import Coq.Strings.String.

Require Import ssreflect ssrbool eqtype.

Local Open Scope string.


Definition prop_stamp_generation (st : State) : Checker :=
    (* whenFail (show st) *) (checker (well_formed st)).

  (*
  Definition propStampGeneration (st : State) :=
    let stamps := generateStamps st in
    whenFail (Checker.trace ("Generated: " ++ nl ++
                             (showStamps (allocated (st_mem st)) stamps)))
             (wellFormed st stamps).
  *)

  Definition prop_generate_indist : Checker :=
    forAllShrink gen_variation_state (fun _ => []) (* shrinkVState *)
                 (fun v => let '(Var lab st1 st2) := v in
                  checker (indist lab st1 st2)).

  Definition prop_fstep_preserves_well_formed (t : table) : Checker :=
    forAllShrinkShow arbitrary (fun _ => []) (* show *)(fun _ => ""%string)
    (fun st =>
    (if well_formed st then
      match fstep t st with
      | Some st' =>
(*
        whenFail ("Initial: " ++ show st ++ nl ++
                  "Step to: " ++ show st' ++ nl)
*)
                 (checker (well_formed st'))
      | _ => checker rejected
      end
    else checker false)).

(* This is trivial, but it was mentioned below so I've proved it *)
Lemma prop_stamp_generation_equiv :
  semCheckable prop_stamp_generation <->
  (forall st, semGen genState st -> well_formed st).
Abort.
(* Proof. *)
(*   rewrite /prop_stamp_generation /semCheckable /checker /testFun. *)
(*   rewrite semForAllShrink. split => H st gen. *)
(*   - specialize (H st gen). by move /semPredQProp/semBool in H. *)
(*   - rewrite semPredQProp. apply /semBool. apply H. exact gen. *)
(* Qed. *)

(* One more rather trivial one;
   TODO both these would become more interesting if we had declarative
        variants of well_formed and indist *)
Lemma prop_generate_indist_equiv :
  semCheckable prop_generate_indist <->
  (forall lab st1 st2,
     semGen gen_variation_state (Var lab st1 st2) -> indist lab st1 st2).
Abort.
(* Proof. *)
(*   rewrite /prop_generate_indist. rewrite semPredQProp. *)
(*   setoid_rewrite semForAllShrink. *)
(*   split => [H lab st1 st2 gen | H [lab st1 st2] gen]. *)
(*   - specialize (H (Var lab st1 st2) gen). red in H. *)
(*     by move /semPredQProp/semBool in H. *)
(*   - rewrite semPredQProp. apply semBool. by apply H. *)
(* Qed. *)

(* One direction of this (soundness) is checked by prop_stamp_generation above;
   this is the high-level spec we need for genState
   TODO: move this to GenerationProofs? *)
Lemma genState_well_formed : forall st,
  semGen genState st <-> well_formed st.
Abort.

Definition fstep_preserves_well_formed : Prop := forall st st',
  well_formed st ->
  fstep default_table st = Some st' ->
  well_formed st'.

Lemma prop_fstep_preserves_well_formed_equiv :
    semChecker (prop_fstep_preserves_well_formed default_table) <->
    fstep_preserves_well_formed.
Abort.
(* Proof. *)
(*   rewrite /prop_fstep_preserves_well_formed /fstep_preserves_well_formed *)
(*     semForAllShrink /arbitrary /arbState. setoid_rewrite semPredQProp. *)
(*   split => [H st st' wf ex | H st arb]. *)
(*   - assert (@genState Pred _ st) as gs by (by rewrite genState_well_formed). *)
(*     specialize (H st gs). *)
(*     rewrite wf ex in H. *)
(*     (* by move /semWhenFail_id /semBool in H. *)     *)
(*     by apply semBool in H. *)
(*   - move /genState_well_formed in arb. rewrite arb. specialize (H st). *)
(*     move : H. case (fstep default_table st) => [ st' | ] H. *)
(*     + specialize (H st' arb Logic.eq_refl). rewrite H. *)
(*       (* rewrite semWhenFail_id. by rewrite <- semBool. *) *)
(*       by apply <- semBool. *)
(*     + fold (semCheckable rejected). rewrite semResult. reflexivity. *)
(* Qed. *)
