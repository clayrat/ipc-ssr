From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap forms derivations normal_forms kripke_trees
                           in_ngamma forces_ngamma le_ks derivable_def.

Section NMinimal.
Context {disp : unit} {A : orderType disp}.

Definition nminimal (work : seq (normal_form A)) (ds : seq (disj A)) (ni : seq (nested_imp A))
                    (ai : atomic_imps A) (a : atoms A) (ctx : seq (form A)) :=
  forall k, Is_Monotone_kripke_tree k ->
    forces_ngamma work ds ni ai a k -> {in ctx, forall c, forces_t k c}.

(*********************************************************************)

Lemma nminimal_derivable_forces work ds ni ai a ctx k :
  Is_Monotone_kripke_tree k ->
  forces_ngamma work ds ni ai a k ->
  nminimal work ds ni ai a ctx ->
  forall c, Derivable ctx c -> forces_t k c.
Proof.
move=>M F N c; case=>t D.
by apply/(soundness_t _ _ _ D _ M)/N.
Qed.

(*********************************************************************)

Lemma nminimal_eqv work ds ni1 ni2 ai a ctx :
  eqv_ni ni1 ni2 ->
  nminimal work ds ni1 ai a ctx -> nminimal work ds ni2 ai a ctx.
Proof.
rewrite /nminimal=>E NM k M F.
by apply: NM=>//; apply/forces_ngamma_eqv/F.
Qed.

(************************************************************************)

Lemma nminimal_shift_work_ds i j work ds ni ai a ctx :
  nminimal (NDisj i j :: work) ds ni ai a ctx ->
  nminimal work ((i, j) :: ds) ni ai a ctx.
Proof.
rewrite /nminimal=>NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ds_work.
Qed.

Lemma nminimal_shift_work_ni x work ds ni ai a ctx :
  nminimal (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a ctx ->
  nminimal work ds (x :: ni) ai a ctx.
Proof.
rewrite /nminimal=>NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ni_work.
Qed.

Lemma nminimal_shift_work_ai i b work ds ni ai a ctx :
  invariant ai ->
  nminimal (AImp i b :: work) ds ni ai a ctx ->
  nminimal work ds ni (update_aimps b i ai) a ctx.
Proof.
rewrite /nminimal=>Ha NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ai_work.
Qed.

(*
Lemma nminimal_shift_work_ai_new i b work ds ni ai a ctx :
  invariant ai -> ~~ lookup ai i ->
  nminimal (AImp i b :: work) ds ni ai a ctx ->
  nminimal work ds ni (update_aimps b i ai) a ctx.
Proof.
rewrite /nminimal=>Ha L NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ai_work_new.
Qed.

Lemma nminimal_shift_work_ai_old i b work ds ni ai a ctx :
  invariant ai -> lookup ai i ->
  nminimal (AImp i b :: work) ds ni ai a ctx ->
  nminimal work ds ni (update_aimps b i ai) a ctx.
Proof.
rewrite /nminimal=>Ha L NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ai_work_old.
Qed.
*)

Lemma nminimal_shift_work_a i work ds ni ai a ctx :
  invariant a ->
  nminimal (NAtom i :: work) ds ni ai a ctx ->
  nminimal work ds ni ai (update_atoms i a) ctx.
Proof.
rewrite /nminimal=>Ha NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_a_work.
Qed.

Lemma nminimal_shift_work_ni_x_ni x work ds ni1 ni2 ai a ctx :
  nminimal (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a ctx ->
  nminimal work ds (ni1 ++ x :: ni2) ai a ctx.
Proof.
rewrite /nminimal=>NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_ni_x_ni_work.
Qed.

Lemma nminimal_shift_ni_x_ni_work x work ds ni1 ni2 ai a ctx :
  nminimal work ds (ni1 ++ x :: ni2) ai a ctx ->
  nminimal (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a ctx.
Proof.
rewrite /nminimal=>NM k M F.
by apply: NM=>//; apply: forces_ngamma_shift_work_ni_x_ni.
Qed.

(********************************************************************)

Lemma nminimal_cons_work_strength b c work ds ni ai a ctx :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_ngamma (c :: work) ds ni ai a k -> forces_t k (nf2form b)) ->
  nminimal (b :: work) ds ni ai a ctx ->
  nminimal (c :: work) ds ni ai a ctx.
Proof.
rewrite /nminimal=>H NM k M F.
apply: NM=>//; apply: (forces_ngamma_cons_work_weak c)=>// F'.
by apply: H.
Qed.

Lemma nminimal_cons_work_weak b c work ds ni ai a ctx :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_t k (nf2form c) -> forces_t k (nf2form b)) ->
  nminimal (b :: work) ds ni ai a ctx ->
  nminimal (c :: work) ds ni ai a ctx.
Proof.
rewrite /nminimal=>H NM k M F.
apply: NM=>//; apply: (forces_ngamma_cons_work_weak c)=>// F'.
by apply: H.
Qed.

Lemma nminimal_shift_work_ai_weak i bs work ds ni ai a ctx :
  invariant ai -> lookup ai i = Some bs ->
  nminimal work ds ni ai a ctx ->
  nminimal (bs ++ work) ds ni (delete i ai) a ctx.
Proof.
rewrite /nminimal=>Ha L NM k M F.
apply: NM=>//; apply: (forces_ngamma_del_ai_rev i bs)=>//.
- move=>n b E; rewrite /nf2form -/nf2form.
  apply: forces_imp_t=>//; apply/F/(In_Work _ _ _ _ _ n).
  by rewrite onth_cat (onth_size E).
by apply: (forces_ngamma_cat_work_tail bs).
Qed.

Lemma nminimal_shift_ds_work_context work c i j ds ni ai a ctx :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_t k (nf2form c) -> forces_t k (OrF (Atom i) (Atom j))) ->
  nminimal work ((i, j) :: ds) ni ai a ctx ->
  nminimal (c :: work) ds ni ai a (nf2form c :: ctx).
Proof.
rewrite /nminimal=>H NM k M F d; rewrite inE; case/orP=>[/eqP{d}->|Hd].
- by apply/F/in_ngamma_cons_work_head.
apply: NM=>//; apply/forces_ngamma_shift_work_ds.
apply/(forces_ngamma_cons_work_weak c)=>// Fc.
by rewrite /nf2form -/nf2form; apply: H.
Qed.

Lemma nminimal_cons_work_cons_context c work ds ni ai a ctx :
  nminimal work ds ni ai a ctx ->
  nminimal (c :: work) ds ni ai a (nf2form c :: ctx).
Proof.
rewrite /nminimal=>NM k M F d; rewrite inE; case/orP=>[/eqP{d}->|Hd].
- by apply/F/in_ngamma_cons_work_head.
by apply: NM=>//; apply/(forces_ngamma_cons_work_tail c).
Qed.

End NMinimal.
