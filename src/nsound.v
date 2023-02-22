From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap forms normal_forms derivations kripke_trees
                           in_ngamma le_ks derivable_def derivable_tools.

Section NSound.
Context {disp : unit} {A : orderType disp}.

Definition nsound (work : seq (normal_form A)) (ds : seq (disj A)) (ni : seq (nested_imp A))
                  (ai : atomic_imps A) (a : atoms A) (ctx : seq (form A)) :=
  forall c, in_ngamma work ds ni ai a c -> Derivable ctx (nf2form c).

Lemma nsound_eqv work ds ni1 ni2 ai a ctx :
  eqv_ni ni1 ni2 ->
  nsound work ds ni1 ai a ctx -> nsound work ds ni2 ai a ctx.
Proof.
rewrite /nsound =>E S c I.
apply/S/in_ngamma_eqv/I.
by rewrite /eqv_ni eq_sym.
Qed.

Lemma nsound_le work ds ni1 ni2 ai a ctx :
  le_ni ni1 ni2 ->
  nsound work ds ni1 ai a ctx -> nsound work ds ni2 ai a ctx.
Proof.
rewrite /nsound =>E S c I.
by apply/S/in_ngamma_ge/I.
Qed.

Lemma nsound_ge work ds ni1 ni2 ai a ctx :
  le_ni ni2 ni1 ->
  nsound work ds ni1 ai a ctx -> nsound work ds ni2 ai a ctx.
Proof.
rewrite /nsound =>E S c I.
by apply/S/in_ngamma_le/I.
Qed.

(***********************************************************************)

Lemma nsound_shift_work_ds i j work ds ni ai a ctx :
  nsound (NDisj i j :: work) ds ni ai a ctx ->
  nsound work ((i, j) :: ds) ni ai a ctx.
Proof.
rewrite /nsound =>S c I.
by apply/S/in_ngamma_shift_ds_work.
Qed.

Lemma nsound_shift_work_ni x work ds ni ai a ctx :
  nsound (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a ctx ->
  nsound work ds (x :: ni) ai a ctx.
Proof.
rewrite /nsound =>S c I.
by apply/S/in_ngamma_shift_ni_work.
Qed.

Lemma nsound_shift_work_ai i b work ds ni ai a ctx :
  invariant ai ->
  nsound (AImp i b :: work) ds ni ai a ctx ->
  nsound work ds ni (update_aimps b i ai) a ctx.
Proof.
rewrite /nsound =>Ha S c I.
by apply/S/in_ngamma_shift_ai_work.
Qed.

Lemma nsound_shift_work_a i work ds ni ai a ctx :
  invariant a ->
  nsound (NAtom i :: work) ds ni ai a ctx ->
  nsound work ds ni ai (update_atoms i a) ctx.
Proof.
rewrite /nsound =>Ha S c I.
by apply/S/in_ngamma_shift_a_work.
Qed.

(* TODO bijection? *)
Lemma nsound_shift_work_ni_x_ni x work ds ni1 ni2 ai a ctx :
  nsound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a ctx ->
  nsound work ds (ni1 ++ x :: ni2) ai a ctx.
Proof.
rewrite /nsound => S c I.
by apply/S/in_ngamma_shift_ni_x_ni_work.
Qed.

Lemma nsound_shift_ni_x_ni_work x work ds ni1 ni2 ai a ctx :
  nsound work ds (ni1 ++ x :: ni2) ai a ctx ->
  nsound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a ctx.
Proof.
rewrite /nsound => S c I.
by apply/S/in_ngamma_shift_work_ni_x_ni.
Qed.

(***********************************************************************)

Remark nsound_cat_work bs work ds ni ai a ctx :
  (forall n b, onth bs n = Some b -> Derivable ctx (nf2form b)) ->
  nsound work ds ni ai a ctx -> nsound (bs ++ work) ds ni ai a ctx.
Proof.
rewrite /nsound => H S c.
case/in_ngamma_work_cat_rev=>[Hi|[n E]].
- by apply: S.
by apply/H/E.
Qed.

Lemma nsound_cons_ds_tail work i j ds ni ai a ctx :
  nsound work ((i, j) :: ds) ni ai a ctx -> nsound work ds ni ai a ctx.
Proof.
rewrite /nsound => S c I.
by apply/S/in_ngamma_cons_ds_tail.
Qed.

Remark nsound_del_ai i work ds ni ai a ctx :
  invariant ai ->
  nsound work ds ni ai a ctx -> nsound work ds ni (delete i ai) a ctx.
Proof.
rewrite /nsound =>Ha S c I.
by apply/S/(in_ngamma_del_ai_tail _ _ _ i).
Qed.

(***********************************************************************)

Lemma nsound_cons_work_cons_ctx c work ds ni ai a ctx :
  nsound work ds ni ai a ctx ->
  nsound (c :: work) ds ni ai a (nf2form c :: ctx).
Proof.
rewrite /nsound =>S d.
case/in_ngamma_cons_work_rev=>[H|{d}->].
- by apply/derivable_weak/S.
by apply/(Derivable_Intro _ _ (Var 0))/ByAssumption.
Qed.

(**********************************************************************)

Lemma nsound_cons_work_weak b c work ds ni ai a ctx :
  (Derivable ctx (nf2form b) -> Derivable ctx (nf2form c)) ->
  nsound (b :: work) ds ni ai a ctx ->
  nsound (c :: work) ds ni ai a ctx.
Proof.
rewrite /nsound =>H S d.
case/in_ngamma_cons_work_rev=>[Hi|{d}->].
- by apply/S/in_ngamma_cons_work_tail.
by apply/H/S/in_ngamma_cons_work_head.
Qed.

Lemma nsound_shift_work_ai_strength i bs work ds ni ai a ctx :
  invariant ai -> invariant a ->
  lookup ai i = Some bs ->
  nsound work ds ni ai (update_atoms i a) ctx ->
  nsound (bs ++ work) ds ni (delete i ai) (update_atoms i a) ctx.
Proof.
move=>Hai Ha L S.
apply/nsound_cat_work=>[n b E|].
- apply: (derivable_a_a_imp_b__derivable_b _ (Atom i)).
  - by apply/(S (NAtom i))/in_ngamma_ins_a_head.
  by apply/(S (AImp i b))/In_Atomic_Imps/E.
by apply: nsound_del_ai.
Qed.

End NSound.