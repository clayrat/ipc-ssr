From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap forms normal_forms derivations kripke_trees
                           in_ngamma forces_ngamma derivable_def derivable_tools catrev le_ks
                           cons_counter_model disjunct ndeco_sound nsound nminimal.

Section NRules.
Context {disp : unit} {A : orderType disp}.

Variant nsearch_spec_result_aux (goal : A) (work : seq (normal_form A))
                                (ds : seq (disj A)) (ni : seq (nested_imp A))
                                (ai : atomic_imps A) (a : atoms A)
                                (ctx : seq (form A)) : Type :=
  | NDerivable of Derivable ctx (Atom goal)
  | NRefutable k of
      Is_Monotone_kripke_tree k &
      forces_ngamma work ds ni ai a k &
      ~ forces_t k (Atom goal).

Variant nsearch_spec_result goal work ds ni ai a ctx : Type :=
  NSearch_Res :
    forall ni1,
    le_ni ni1 ni ->
    deco_sound work ds ni1 ai a ->
    nsearch_spec_result_aux goal work ds ni1 ai a ctx ->
    nsearch_spec_result goal work ds ni ai a ctx.

Definition nsearch_spec goal work ds ni ai a ctx : Type :=
  deco_sound work ds ni ai a ->
  nsound work ds ni ai a ctx ->
  nminimal work ds ni ai a ctx ->
  nsearch_spec_result goal work ds ni ai a ctx.

(**********************************************************************)

Lemma fail i dni ai a ctx :
  a_ai_disj a ai ->
  a_goal_disj a i ->
  nsearch_spec i [::] [::] (rev_d dni) ai a ctx.
Proof.
rewrite /nsearch_spec=>Ai Ag C S M.
apply: (NSearch_Res _ _ _ _ _ _ _ (rev_d dni))=>//.
- by exact: le_ni_refl.
case: (cons_counter_model _ _ _ _ C Ai Ag)=>k [Mk Fk Nk].
by apply: (NRefutable _ _ _ _ _ _ _ k).
Qed.

(**********************************************************************)

Lemma rule_shift_work_ds goal i j work ds ni ai a ctx :
  nsearch_spec goal work ((i, j) :: ds) ni ai a ctx ->
  nsearch_spec goal (NDisj i j :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec=>P C S M.
case: P.
- by apply: deco_sound_shift_work_ds.
- by apply: nsound_shift_work_ds.
- by apply: nminimal_shift_work_ds.
move=>ni1 L1 C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ ni1)=>//.
- by apply: deco_sound_shift_ds_work.
case: S1; first by apply: NDerivable.
move=>k Mk Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
by apply: forces_ngamma_shift_ds_work.
Qed.

Lemma rule_shift_work_ni0 goal x work ds ni ai a ctx :
  nsearch_spec goal work ds (Undecorated x :: ni) ai a ctx ->
  nsearch_spec goal (NImp_NF x :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec=>P C S M.
case: P.
- by apply: deco_sound_shift_work_ni0.
- by apply: nsound_shift_work_ni.
- by apply: nminimal_shift_work_ni.
move=>ni1 L1 C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ (behead ni1)).
- by case: {C1 S1}ni1 L1=>//=; case=>[z|z _] s; case/andP.
- by case: {S1}ni1 L1 C1=>//=; case=>[z|z k] s; case/andP=>/eqP{z}-> _;
  apply: deco_sound_shift_ni_work.
case: S1; first by apply: NDerivable.
move=> k Mk Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
case: {C1}ni1 L1 Fk=>//=; case=>[z|z q] s; case/andP=>/eqP{z}-> _;
by apply: forces_ngamma_shift_ni_work.
Qed.

Lemma rule_shift_work_ai goal i b work ds ni ai a ctx :
  invariant ai ->
  nsearch_spec goal work ds ni (update_aimps b i ai).1 a ctx ->
  nsearch_spec goal (AImp i b :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec =>Hai H C S M.
case: H.
- by apply: deco_sound_shift_work_ai.
- by apply: nsound_shift_work_ai.
- by apply: nminimal_shift_work_ai.
move=>ni1 Ln C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ ni1)=>//.
- by apply: deco_sound_shift_ai_work.
case: S1; first by apply: NDerivable.
move=>k Mf Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
by apply/forces_ngamma_shift_ai_work.
Qed.

Lemma rule_shift_work_a goal i work ds ni ai a a' ctx :
  invariant a ->
  a' = (update_atoms i a).1 ->                  (* fording to force a let-binding at the call site *)
  nsearch_spec goal work ds ni ai a' ctx ->
  nsearch_spec goal (NAtom i :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec =>Ha Ea H C S M.
case: H.
- by rewrite Ea; apply: deco_sound_shift_work_a.
- by apply: (nsound_shift_work_a i _ _ _ _ a a').
- by rewrite Ea; apply: nminimal_shift_work_a.
rewrite Ea=>ni1 Ln C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ ni1)=>//.
- by apply: deco_sound_shift_a_work.
case: S1; first by apply: NDerivable.
move=>k Mf Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
by apply/forces_ngamma_shift_a_work.
Qed.

Lemma shift_ni_dni goal work ds x k ni dni ai a ctx :
  nsearch_spec goal work ds (catrev_d ((x, k) :: dni) ni) ai a ctx ->
  nsearch_spec goal work ds (catrev_d dni (Decorated x k :: ni)) ai a ctx.
Proof. by []. Qed.

(*************************************************************************)

Lemma nax goal work ds ni ai a ctx :
  in_ngamma work ds ni ai a (NAtom goal) ->
  nsearch_spec goal work ds ni ai a ctx.
Proof.
rewrite /nsearch_spec=>H C S M.
apply: (NSearch_Res _ _ _ _ _ _ _ ni)=>//; first by exact: le_ni_refl.
by apply/NDerivable/(S (NAtom goal)).
Qed.

(**********************************************************************)

Lemma nefq goal work ds ni ai a ctx :
  nsearch_spec goal (NFalsum :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec=>C S M.
apply: (NSearch_Res _ _ _ _ _ _ _ ni)=>//; first by exact: le_ni_refl.
case: (S NFalsum); first by apply: in_ngamma_cons_work_head.
rewrite /nf2form => t D; apply/NDerivable/(Derivable_Intro _ _ (Efq t (Atom goal))).
by apply: ByAbsurdity.
Qed.

Lemma contradiction_atoms goal i work ds ni ai a ctx :
  invariant a -> lookup a i ->
  nsearch_spec goal work ds ni ai a ctx ->
  nsearch_spec goal (NAtom i :: work) ds ni ai a ctx.
Proof.
move=>Ha L H.
apply: (rule_shift_work_a goal i _ _ _ _ a a)=>//.
by apply/esym/upsert_const=>//; case/optP: L=>[[]].
Qed.

(**************************************************************************)

Lemma left_p_imp_work goal i b work ds ni ai a ctx :
  lookup a i ->
  nsearch_spec goal (b :: work) ds ni ai a ctx ->
  nsearch_spec goal (AImp i b :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec =>L H C S M.
case: H.
- apply: (deco_sound_cons_work_strength (AImp i b))=>// k Mk Fk.
  apply: (forces_imp_app_t _ (Atom i)).
  - by apply/(Fk (NAtom i))/In_Atoms.
  by apply/(Fk (AImp i b))/in_ngamma_cons_work_head.
- apply/(nsound_cons_work_weak (AImp i b))=>//.
  rewrite {1}/nf2form -/nf2form =>Dab.
  apply: (derivable_a_a_imp_b__derivable_b _ (Atom i))=>//.
  by apply/(S (NAtom i))/In_Atoms.
- apply: (nminimal_cons_work_weak (AImp i b))=>// k Mk Fk.
  rewrite {1}/nf2form -/nf2form.
  by apply: forces_imp_t.
move=>ni1 Ln C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ ni1)=>//.
- apply: (deco_sound_cons_work_weak b)=>// k Mk Fk.
  rewrite {1}/nf2form -/nf2form.
  by apply: forces_imp_t.
case: S1; first by apply NDerivable.
move=>k Mk Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
apply: (forces_ngamma_cons_work_weak b)=>// Fb.
rewrite {1}/nf2form -/nf2form.
by apply: forces_imp_t.
Qed.


(****************************************************************)

Lemma left_p_imp_ai goal i work ds ni bs ai ai' a a' ctx :
  invariant ai -> invariant a ->
  lookup ai i = Some bs ->
  ai' = (delete i ai).1 ->      (* fording to force a let-binding at the call site *)
  a' = (update_atoms i a).1 ->
  nsearch_spec goal (bs ++ work) ds ni ai' a' ctx ->
  nsearch_spec goal (NAtom i :: work) ds ni ai a ctx.
Proof.
rewrite /nsearch_spec =>Hai Ha L Eai Ea H C S M.
case: H.
- rewrite Eai Ea; apply: deco_sound_shift_work_ai_strength=>//.
  by apply: deco_sound_shift_work_a.
- apply: (nsound_shift_work_ai_strength i _ _ _ _ ai ai' a a')=>//.
  by apply: (nsound_shift_work_a i _ _ _ _ a a').
- rewrite Eai Ea; apply: nminimal_shift_work_ai_weak=>//.
  by apply: nminimal_shift_work_a.
rewrite Eai Ea=>ni1 Ln C1 S1.
apply: (NSearch_Res _ _ _ _ _ _ _ ni1)=>//.
- apply: deco_sound_shift_a_work=>//.
  by apply: (deco_sound_shift_work_ai_weak i bs).
case: S1; first by apply NDerivable.
move=>k Mk Fk Nk.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
apply: forces_ngamma_shift_a_work=>//.
by apply: (forces_ngamma_shift_work_ai_weak i bs).
Qed.

(****************************************************************)

Lemma left_disj goal work i j ds ni ai a ctx :
  (forall ni1, le_ni ni ni1 ->
   nsearch_spec goal (NAtom i :: work) ds ni1 ai a (Atom i :: ctx)) ->
  (forall ni2, eqv_ni ni2 ni ->
   nsearch_spec goal (NAtom j :: work) ds ni2 ai a (Atom j :: ctx)) ->
  nsearch_spec goal work ((i, j) :: ds) ni ai a ctx.
Proof.
rewrite /nsearch_spec =>Hl He C S M.
case: (filter_deco i ni)=>ni1 [L1 Fi].
case: (Hl ni1)=>//.
- apply: deco_sound_filter_deco=>//.
  apply: (deco_sound_le _ _ ni)=>//.
  by apply/deco_sound_cons_ds_tail/C.
- apply: (nsound_le _ _ ni)=>//.
  apply: nsound_cons_work_cons_ctx.
  by apply/nsound_cons_ds_tail/S.
- apply: (nminimal_eqv _ _ ni); first by apply: le_eqv.
  apply: (nminimal_shift_ds_work_ctx _ (NAtom i) i j)=>// k Mk.
  by rewrite /nf2form -/nf2form=>F; left.
move=>{Fi} ni2 Ln2 C2 S2.
case: (inf_deco ni ni2).
- by apply: (eqv_ni_trans ni1); [apply: le_eqv | apply: ge_eqv].
move=> ni3 [Ln3 Le32 I3].
case: S2.
- (* left premiss yields a derivation *)
  move=>D2.
  case: (filter_deco j ni3)=>ni4 [L4 Fj].
  case: (He ni4).
  - by apply: (eqv_ni_trans ni3); [apply: ge_eqv | apply le_eqv].
  - apply: deco_sound_filter_deco=>//.
    apply: (deco_sound_le _ _ ni3)=>//.
    apply: (deco_sound_inf _ _ _ ni ni2)=>//.
    - by apply: (deco_sound_cons_ds_tail _ i j).
    by apply: (deco_sound_cons_work_tail (NAtom i)).
  - apply: (nsound_eqv _ _ ni).
    - by apply: (eqv_ni_trans ni3); [apply: ge_eqv | apply le_eqv].
    apply: nsound_cons_work_cons_ctx.
    by apply: (nsound_cons_ds_tail _ i j).
  - apply: (nminimal_eqv _ _ ni).
    - by apply: (eqv_ni_trans ni3); [apply: ge_eqv | apply le_eqv].
    apply: (nminimal_shift_ds_work_ctx _ (NAtom j) i j)=>// k Mk.
    by rewrite /nf2form -/nf2form=>F; right.
  move=>ni5 Ln5 C5 S5.
  case: (inf_deco ni ni5).
  - apply: (eqv_ni_trans ni4); last by apply: ge_eqv.
    by apply: (eqv_ni_trans ni3); [apply: ge_eqv | apply: le_eqv].
  move=>ni6 [Ln6 Le65 I6].
  apply: (NSearch_Res _ _ _ _ _ _ _ ni6)=>//.
  - apply: (deco_sound_inf _ _ _ ni ni5)=>//.
    apply: deco_sound_shift_work_ds.
    apply: (deco_sound_cons_work_weak (NAtom j))=>// k Mk.
    by rewrite /nf2form -/nf2form=>F; right.
  case: S5.
  - move=>D5.
    apply: NDerivable.
    case: D2=>s Ds.
    case: D5=>t Dt.
    case: (S (NDisj i j)); first by apply: (In_Disjs _ _ _ _ _ 0).
    move=>r; rewrite /nf2form -/nf2form=> Dr.
    by apply/(Derivable_Intro _ _ (Cas (Atom i) (Atom j) r s t))/OrFElim.
  move=>k Mk Fk Nk.
  apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
  apply: (forces_ngamma_eqv _ ni5)=>//.
  apply: forces_ngamma_shift_work_ds.
  apply: (forces_ngamma_cons_work_weak (NAtom j))=>//.
  by rewrite /nf2form -/nf2form=>F; right.
(* left premiss yields a counter-model *)
move=>k Mk Fk Nk.
apply: (NSearch_Res _ _ _ _ _ _ _ ni3)=>//.
- apply: (deco_sound_inf _ _ _ ni ni2)=>//.
  apply: deco_sound_shift_work_ds.
  apply: (deco_sound_cons_work_weak (NAtom i))=>// k1 Mk1.
  by rewrite /nf2form -/nf2form=>F; left.
apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
apply: (forces_ngamma_eqv _ ni2)=>//.
apply: forces_ngamma_shift_work_ds.
apply: (forces_ngamma_cons_work_weak (NAtom i))=>//.
by rewrite /nf2form -/nf2form=>F; left.
Qed.

(**********************************************************************)

Lemma left_nimp goal work ds a0 a1 b ni dni ai a ctx :
  (forall ni1, le_ni (catrev_d dni ni) ni1 ->
   nsearch_spec a1 (AImp a1 b :: NAtom a0 :: work) ds ni1 ai a (Atom a0 :: ctx)) ->
  (forall ni1, le_ni ni1 (catrev_d dni ni) ->
   nsearch_spec goal (b :: work) ds ni1 ai a ctx) ->
  (forall ni1 k, le_ni ni1 (catrev_d ((NImp a0 a1 b, k) :: dni) ni) ->
   nsearch_spec goal work ds ni1 ai a ctx) ->
  nsearch_spec goal work ds (catrev_d dni (Undecorated (NImp a0 a1 b) :: ni)) ai a ctx.
Proof.
rewrite /nsearch_spec =>Hl Hr Hf C S M.
set dnn := catrev_d dni ni.
case: (filter_deco a0 dnn)=>ni1 [Ln1 Fa0].
case: (Hl ni1)=>//.
- apply: (deco_sound_cons_work_strength (NImp_NF (NImp a0 a1 b))).
  - rewrite /nf2form -/nf2form => k Mk Fk.
    apply: (forces_imp_imp_fro_t _ (Atom a0))=>//.
    - by apply/(Fk (NAtom a0))/in_ngamma_cons_work_tail/in_ngamma_cons_work_head.
    apply/(Fk (NImp_NF (NImp a0 a1 b)))/in_ngamma_cons_work_head.
  apply: (deco_sound_shift_ni_work (Undecorated (NImp a0 a1 b))).
  apply: deco_sound_filter_deco=>//.
  apply: deco_sound_shift_work_ni0.
  apply: (deco_sound_le _ _ dnn)=>//.
  rewrite /dnn (rev_app_app dni ni).
  apply: (deco_sound_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
  by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
- apply: (nsound_le _ _ dnn)=>//.
  apply: (nsound_cons_work_weak (NImp_NF (NImp a0 a1 b))).
  - rewrite /nf2form -/nf2form; case=>t Dt.
    apply: (Derivable_Intro _ _ (Abs (Atom a1)
                                (App (Imp (Atom a0) (Atom a1))
                                     (Shift t)
                                     (Abs (Atom a0) (Shift (Var 0)))))).
    apply/ImpIntro/ImpElim; first by apply: ShiftIntro.
    by apply/ImpIntro/ShiftIntro/ByAssumption.
  rewrite /dnn (rev_app_app dni ni).
  apply: (nsound_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
  apply: (nsound_cons_work_cons_ctx (NAtom a0)).
  by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
- apply: (nminimal_eqv _ _ dnn); first by apply: le_eqv.
  apply: (nminimal_cons_work_strength (NImp_NF (NImp a0 a1 b))).
  - move=>k Mk Fk; rewrite /nf2form -/nf2form.
    apply: forces_imp_imp_to_t=>//.
    - by apply/(Fk (NAtom a0))/in_ngamma_cons_work_tail/in_ngamma_cons_work_head.
    rewrite (_ : Imp (Atom a1) (nf2form b) = nf2form (AImp a1 b)) //.
    by apply/Fk/in_ngamma_cons_work_head.
  rewrite /dnn (rev_app_app dni ni).
  apply: (nminimal_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
  apply: (nminimal_cons_work_cons_ctx (NAtom a0)).
  by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
move=>ni2 Ln2 C2 S2.
case: (inf_deco dnn ni2).
- by apply/(eqv_ni_trans ni1); [apply: le_eqv | apply: ge_eqv].
move=>ni3 [Ln3 E3 I3].
case: S2.
- (* left_premiss yields a derivation *)
  move=>D01.
  case: (Hr ni3)=>//.
  - apply: (deco_sound_inf _ _ _ dnn ni2)=>//.
    - apply: (deco_sound_cons_work_strength (NImp_NF (NImp a0 a1 b))).
      - move=>k Mk Fk.
        apply: (forces_imp_app_t _ (Imp (Atom a0) (Atom a1))).
        - apply: (nminimal_derivable_forces work ds
                   (catrev_d dni (Undecorated (NImp a0 a1 b) :: ni)) ai a ctx)=>//.
          - rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
            apply: forces_ngamma_shift_work_ni_x_ni=>/=.
            by rewrite -(rev_app_app dni ni).
          apply: derivable_a_context_b__derivable_a_imp_b=>//.
        by apply/(Fk (NImp_NF (NImp a0 a1 b)))/in_ngamma_cons_work_head.
      rewrite /dnn (rev_app_app dni ni).
      apply: (deco_sound_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
      by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
    apply: (deco_sound_cons_work_strength (NImp_NF (NImp a0 a1 b))).
    - move=>k Mk Fk.
      apply: (forces_imp_app_t _ (Imp (Atom a0) (Atom a1))).
      - apply: (nminimal_derivable_forces work ds
                 (catrev_d dni (Undecorated (NImp a0 a1 b) :: ni)) ai a ctx)=>//.
        - rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
          apply: forces_ngamma_shift_work_ni_x_ni.
          apply: (forces_ngamma_eqv _ ni2)=>//.
          apply: (eqv_ni_trans ni1); last by apply: ge_eqv.
          rewrite -(rev_app_app dni ni) -/dnn.
          by apply: le_eqv.
        by apply: derivable_a_context_b__derivable_a_imp_b.
      by apply/(Fk (NImp_NF (NImp a0 a1 b)))/in_ngamma_cons_work_head.
    apply: (deco_sound_cons_work_weak2 (AImp a1 b) (NAtom a0))=>// k Mk.
    rewrite /nf2form -/nf2form=>/[swap].
    by apply: forces_imp_imp_to_t.
  - apply: (nsound_ge _ _ dnn)=>//.
    apply: (nsound_cons_work_weak (NImp_NF (NImp a0 a1 b))).
    - rewrite /nf2form -/nf2form =>D.
      apply: (derivable_a_a_imp_b__derivable_b _ (Imp (Atom a0) (Atom a1)))=>//.
      by apply: derivable_a_context_b__derivable_a_imp_b.
    rewrite /dnn (rev_app_app dni ni).
    apply: (nsound_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
    by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
  - apply: (nminimal_eqv _ _ dnn); first by apply: ge_eqv.
    apply: (nminimal_cons_work_weak (NImp_NF (NImp a0 a1 b))).
    - rewrite /nf2form -/nf2form=>k Mk Fk.
      by apply: (forces_imp_t).
    rewrite /dnn (rev_app_app dni ni).
    apply: (nminimal_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
    by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
  move=>ni4 Ln4 C4 S4.
  case: (le_app0 ni4 (rev_d dni) ni).
  - rewrite -(rev_app_app dni ni) -/dnn.
    by apply: (le_ni_trans ni3).
  move=>[ni41 ni42] /= [E4 Es].
  apply: (NSearch_Res _ _ _ _ _ _ _ (ni41 ++ Undecorated (NImp a0 a1 b) :: ni42)).
  - rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
    apply: le_ni_app_nn=>//.
    rewrite -E4 -(rev_app_app dni ni) -/dnn.
    by apply: (le_ni_trans ni3).
  - apply: deco_sound_shift_work_ninni; rewrite -E4.
    apply: (deco_sound_cons_work_weak b)=>//.
    rewrite /nf2form -/nf2form=>k Mk Fk.
    by apply: forces_imp_t.
  case: S4; first by apply: NDerivable.
  move=>k Mk Fk Nk.
  apply: (NRefutable _ _ _ _ _ _ _ k)=>//.
  apply: forces_ngamma_shift_work_ni_x_ni.
  rewrite -E4.
  apply: (forces_ngamma_cons_work_weak b)=>//= F.
  rewrite /nf2form -/nf2form.
  by apply: forces_imp_t.
(* left premiss yields a counter-model *)
move=>k Mk Fk Nk.
case: (le_app0 ni3 (rev_d dni) ni); first by rewrite -(rev_app_app dni ni).
move=>[ni31 ni32]/= [E3' Es].
case: (Hf (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32) k)=>/=.
- rewrite (rev_app_app dni (Decorated (NImp a0 a1 b) k :: ni)).
  apply: le_ni_app_dd=>//.
  by rewrite -E3' -(rev_app_app dni ni).
- apply: deco_sound_shift_work_nirni.
  - split=>//.
    - apply: forces_ngamma_shift_work_ni_x_ni.
      rewrite -E3'.
      apply: (forces_ngamma_cons_work_weak2 (AImp a1 b) (NAtom a0))=>//=.
      - rewrite /nf2form -/nf2form=>/[swap].
        by apply: forces_imp_imp_to_t.
      by apply: (forces_ngamma_eqv _ ni2).
    move: Nk=>/[swap] Fa01; apply; apply/forces_imp_app_t/Fa01.
    by apply/(Fk (NAtom a0))/in_ngamma_cons_work_tail/in_ngamma_cons_work_head.
  rewrite -E3'.
  apply: (deco_sound_inf _ _ _ dnn ni2)=>//.
  - rewrite /dnn (rev_app_app dni ni).
    apply: (deco_sound_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
    by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
  apply: (deco_sound_cons_work_weak2 (AImp a1 b) (NAtom a0))=>// k1 Mk1.
  rewrite /nf2form -/nf2form=>/[swap].
  by apply: forces_imp_imp_to_t.
- rewrite /nsound=>c Hc.
  apply: S; case: Hc.
  - by move=>n x E; apply: (In_Work _ _ _ _ _ n).
  - by move=> n i j E; apply: (In_Disjs _ _ _ _ _ n).
  - move=>n x E; apply: (In_Nested_Imps _ _ _ _ _ n).
    rewrite -(eqv_nimps_eq (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32)
      (catrev_d dni (Undecorated (NImp a0 a1 b) :: ni))) //.
    rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
    apply/le_eqv/le_ni_app_dn=>//.
    by rewrite -E3' -(rev_app_app dni ni).
  - by move=>i b0 n bs L E; apply (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
  by move=>i L; apply In_Atoms.
- apply: nminimal_shift_work_ni_x_ni.
  rewrite -E3'.
  apply: (nminimal_eqv _ _ dnn); first by apply ge_eqv.
  rewrite /dnn (rev_app_app dni ni).
  apply: (nminimal_shift_ni_x_ni_work (Undecorated (NImp a0 a1 b))).
  by rewrite -(rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
move=>ni5 Ln5 C5 S5.
apply: (NSearch_Res _ _ _ _ _ _ _ ni5)=>//.
apply: (le_ni_trans (ni31 ++ Decorated (NImp a0 a1 b) k :: ni32))=>//.
rewrite (rev_app_app dni (Undecorated (NImp a0 a1 b) :: ni)).
apply: le_ni_app_dn=>//.
by rewrite -E3' -(rev_app_app dni ni).
Qed.

End NRules.
