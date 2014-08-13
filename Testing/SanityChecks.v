Require Import QuickChick.

Require Import Reachability.
Require Import Printing.
Require Import SingleStateArb.
Require Import Indist.
Require Import Shrinking.
Require Import Generation.
Require Import Machine.

Require Import List.
Require Import Common.
Require Import String.

Require Import ssreflect ssrbool eqtype.

Local Open Scope string.

Section Checkers.
  Context {Gen : Type -> Type}
          {H : GenMonad Gen}.

  (* Sanity check for stamp generation *)
  Definition prop_stamp_generation (st : State) : Property Gen :=
    (* whenFail (show st) *) (property (well_formed st)).

  (*
  Definition propStampGeneration (st : State) :=
    let stamps := generateStamps st in
    whenFail (Property.trace ("Generated: " ++ nl ++
                             (showStamps (allocated (st_mem st)) stamps)))
             (wellFormed st stamps).
  *)

  Definition prop_generate_indist : Property Gen :=
    forAllShrink show gen_variation_state (fun _ => []) (* shrinkVState *)
                 (fun v => let '(Var lab st1 st2) := v in
                  property (indist lab st1 st2) : Gen QProp).

  Definition prop_exec_preserves_well_formed (t : table) : Property Gen :=
    forAllShrink (* show *)(fun _ => ""%string) arbitrary (fun _ => []) (fun st =>
    (if well_formed st then
      match exec t st with
      | Some (_, st') =>
(*
        whenFail ("Initial: " ++ show st ++ nl ++
                  "Step to: " ++ show st' ++ nl)
*)
                 (property (well_formed st'))
      | _ => property rejected
      end
    else property false) : Gen QProp).

End Checkers.

(* TODO: get a way to still run these tests!
Definition xxx := forAll show arbitrary (prop_stamp_generation : State -> Gen.Gen QProp).
QuickCheck xxx. Could not run test
*)

Require Import EndToEnd SetOfOutcomes.

(* This is rather trivial, but it was mentioned below so I've proved it *)
Lemma prop_stamp_generation_equiv :
  semTestable (prop_stamp_generation : State -> Pred QProp) <->
  (forall st, @genState Pred _ st -> well_formed st).
Proof.
  rewrite /prop_stamp_generation /semTestable /property /testFun.
  setoid_rewrite semForAllShrink. split => H st gen.
  - specialize (H st gen). by move /semPredQProp/semBool in H.
  - rewrite semPredQProp. setoid_rewrite <- semBool. apply H. exact gen.
Qed.

(* One direction of this (soundness) is checked by prop_stamp_generation above;
   this is the high-level spec we need for genState *)
Lemma genState_well_formed : forall st,
  @genState Pred _ st <-> well_formed st.
Admitted.

Definition exec_preserves_well_formed t : Prop := forall st x st',
  well_formed st ->
  exec t st = Some (x, st') ->
  well_formed st'.

Lemma prop_exec_preserves_well_formed_equiv :
  forall (t : table),
    semProperty (@prop_exec_preserves_well_formed Pred _ t) <->
    exec_preserves_well_formed t.
Proof.
  move => t.
  rewrite /prop_exec_preserves_well_formed /exec_preserves_well_formed
    semForAllShrink /arbitrary /arbState. setoid_rewrite semPredQProp.
  split => [H st tr st' wf ex | H st arb].
  - assert (@genState Pred _ st) as gs by (by rewrite genState_well_formed).
    specialize (H st gs).
    rewrite wf ex in H.
    (* by move /semWhenFail_idemp /semBool in H. *)    
    by setoid_rewrite <- semBool in H.
  - move /genState_well_formed in arb. rewrite arb. specialize (H st).
    move : H. case (exec t st) => [ [tr st'] | ] H.
    + specialize (H tr st' arb Logic.eq_refl). rewrite H.
      (* rewrite semWhenFail_idemp. by rewrite <- semBool. *)
      by setoid_rewrite <- semBool.
    + fold (semTestable rejected). rewrite <- semResult. reflexivity.
Qed.
