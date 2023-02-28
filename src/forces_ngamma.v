From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq order.
From ipcssr Require Import prelude avlmap forms normal_forms kripke_trees in_ngamma le_ks.

Section Forces_NGamma.
Context {disp : unit} {A : orderType disp}.

Definition forces_ngamma (work : seq (normal_form A)) (ds : seq (disj A))
                         (ni : seq (nested_imp A)) (ai : atomic_imps A) (a : atoms A)
                         (k : kripke_tree A) :=
  forall c,
  in_ngamma work ds ni ai a c -> forces_t k (nf2form c).

(********************************************************************)

Lemma forces_ngamma_cons_work c work ds ni ai a k :
  forces_t k (nf2form c) ->
  forces_ngamma work ds ni ai a k ->
  forces_ngamma (c :: work) ds ni ai a k.
Proof.
move=>Fa Fn c0 I.
case: (in_ngamma_cons_work_rev _ _ _ _ _ _ _ I)=>[H|->] //.
by apply: Fn.
Qed.

Lemma forces_ngamma_cons_work_tail c work ds ni ai a k :
  forces_ngamma (c :: work) ds ni ai a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Fn c0 I.
by apply/Fn/in_ngamma_cons_work_tail.
Qed.

Remark forces_ngamma_cat_work bs work ds ni ai a k :
  (forall n b, onth bs n = Some b -> forces_t k (nf2form b)) ->
  forces_ngamma work ds ni ai a k -> forces_ngamma (bs ++ work) ds ni ai a k.
Proof.
move=>Hf Fn c I.
case: (in_ngamma_work_cat_rev _ _ _ _ _ _ _ I)=>[H|[n E]].
- by apply: Fn.
by apply: (Hf _ _ E).
Qed.

Lemma forces_ngamma_cat_work_tail bs work ds ni ai a k :
  forces_ngamma (bs ++ work) ds ni ai a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_work_catl.
Qed.

Lemma forces_ngamma_cons_ds_tail work i j ds ni ai a  k :
  forces_ngamma work ((i, j) :: ds) ni ai a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_cons_ds_tail.
Qed.

Lemma forces_ngamma_cons_ni_tail work ds x ni ai a k :
  forces_ngamma work ds (x :: ni) ai a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_cons_ni_tail.
Qed.

Remark forces_ngamma_del_ai i work ds ni ai a k :
  invariant ai ->
  forces_ngamma work ds ni ai a k ->
  forces_ngamma work ds ni (delete i ai).1 a k.
Proof.
move=>Ha Fn c I.
by apply/Fn/in_ngamma_del_ai_tail/I.
Qed.

Lemma forces_ngamma_del_ai_rev i bs work ds ni ai a k :
  invariant ai ->
  lookup ai i = Some bs ->
  (forall n b, onth bs n = Some b -> forces_t k (nf2form (AImp i b))) ->
  forces_ngamma work ds ni (delete i ai).1 a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Ha L Hn Fn c I.
case: (in_ngamma_del_ai_rev _ _ _ _ _ _ _ _ _ L I)=>// P.
- by apply: Fn.
by case: P=>b [n][E Ec]; rewrite Ec; apply/Hn/E.
Qed.

(***********************************************************************)

Lemma forces_ngamma_eqv ni1 ni2 work ds ai a k :
  eqv_ni ni1 ni2 ->
  forces_ngamma work ds ni2 ai a k ->
  forces_ngamma work ds ni1 ai a k.
Proof.
move=>E Fn c I.
by apply/Fn/in_ngamma_eqv/I.
Qed.

(***********************************************************************)

(* TODO roll into bijections? *)

Lemma forces_ngamma_shift_ds_work i j work ds ni ai a k :
  forces_ngamma work ((i, j) :: ds) ni ai a k ->
  forces_ngamma (NDisj i j :: work) ds ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_work_ds.
Qed.

Lemma forces_ngamma_shift_work_ds i j work ds ni ai a k :
  forces_ngamma (NDisj i j :: work) ds ni ai a k ->
  forces_ngamma work ((i, j) :: ds) ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_ds_work.
Qed.

Lemma forces_ngamma_shift_ni_work x work ds ni ai a k :
  forces_ngamma work ds (x :: ni) ai a k ->
  forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_work_ni.
Qed.

Lemma forces_ngamma_shift_work_ni x work ds ni ai a k :
  forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a k ->
  forces_ngamma work ds (x :: ni) ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_ni_work.
Qed.

Lemma forces_ngamma_shift_ai_work i b work ds ni ai a k :
  invariant ai ->
  forces_ngamma work ds ni (update_aimps b i ai).1 a k ->
  forces_ngamma (AImp i b :: work) ds ni ai a k.
Proof.
move=>Ha; case/boolP: (lookup ai i)=>[/optP [bs] L|N] Fn c I.
- by apply/Fn/(in_ngamma_shift_work_ai_old _ _ _ _ _ bs).
by apply/Fn/in_ngamma_shift_work_ai_new.
Qed.

(*
Lemma forces_ngamma_shift_ai_work_new i b work ds ni ai a k :
  invariant ai ->
  ~~ lookup ai i ->
  forces_ngamma work ds ni (update_aimps b i ai) a k ->
  forces_ngamma (AImp i b :: work) ds ni ai a k.
Proof.
move=>Ha N Fn c I.
by apply/Fn/in_ngamma_shift_work_ai_new.
Qed.

Lemma forces_ngamma_shift_ai_work_old i b work ds ni ai a k :
  invariant ai ->
  lookup ai i ->
  forces_ngamma work ds ni (update_aimps b i ai) a k ->
  forces_ngamma (AImp i b :: work) ds ni ai a k.
Proof.
move=>Ha /optP [ns E] Fn c I.
by apply/Fn/(in_ngamma_shift_work_ai_old _ _ _ _ _ ns).
Qed.
*)

Lemma forces_ngamma_shift_work_ai i b work ds ni ai a k :
  invariant ai ->
  forces_ngamma (AImp i b :: work) ds ni ai a k ->
  forces_ngamma work ds ni (update_aimps b i ai).1 a k.
Proof.
move=>Ha Fn c I.
by apply/Fn/in_ngamma_shift_ai_work.
Qed.

Lemma forces_ngamma_shift_a_work i work ds ni ai a k :
  invariant a ->
  forces_ngamma work ds ni ai (update_atoms i a).1 k ->
  forces_ngamma (NAtom i :: work) ds ni ai a k.
Proof.
move=>Ha Fn c I.
by apply/Fn/in_ngamma_shift_work_a.
Qed.

Lemma forces_ngamma_shift_work_a i work ds ni ai a k :
  invariant a ->
  forces_ngamma (NAtom i :: work) ds ni ai a k ->
  forces_ngamma work ds ni ai (update_atoms i a).1 k.
Proof.
move=>Ha Fn c I.
by apply/Fn/in_ngamma_shift_a_work.
Qed.

Lemma forces_ngamma_shift_work_ni_x_ni x work ds ni1 ni2 ai a k :
  forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a k ->
  forces_ngamma work ds (ni1 ++ x :: ni2) ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_ni_x_ni_work.
Qed.

Lemma forces_ngamma_shift_ni_x_ni_work x work ds ni1 ni2 ai a k :
  forces_ngamma work ds (ni1 ++ x :: ni2) ai a k ->
  forces_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a k.
Proof.
move=>Fn c I.
by apply/Fn/in_ngamma_shift_work_ni_x_ni.
Qed.

(********************************************************************)

Lemma forces_ngamma_cons_work_weak b c work ds ni ai a k :
  Is_Monotone_kripke_tree k ->
  (forces_t k (nf2form b) -> forces_t k (nf2form c)) ->
  forces_ngamma (b :: work) ds ni ai a k ->
  forces_ngamma (c :: work) ds ni ai a k.
Proof.
move=>M Fbc Fn; apply: forces_ngamma_cons_work.
- by apply/Fbc/Fn/in_ngamma_cons_work_head.
by apply/forces_ngamma_cons_work_tail/Fn.
Qed.

Lemma forces_ngamma_cons_work_weak2 b c d work ds ni ai a k :
  Is_Monotone_kripke_tree k ->
  (forces_t k (nf2form b) -> forces_t k (nf2form c) -> forces_t k (nf2form d)) ->
  forces_ngamma (b :: c :: work) ds ni ai a k ->
  forces_ngamma (d :: work) ds ni ai a k.
Proof.
move=>M Fbcd Fn; apply: forces_ngamma_cons_work.
- apply/Fbcd/Fn.
  - by apply/Fn/in_ngamma_cons_work_head.
  by apply/in_ngamma_cons_work_tail/in_ngamma_cons_work_head.
by apply/(forces_ngamma_cons_work_tail c)/(forces_ngamma_cons_work_tail b).
Qed.

Lemma forces_ngamma_shift_work_ai_weak i bs work ds ni ai a k :
  invariant ai ->
  Is_Monotone_kripke_tree k ->
  lookup ai i = Some bs ->
  forces_ngamma (bs ++ work) ds ni (delete i ai).1 a k ->
  forces_ngamma work ds ni ai a k.
Proof.
move=>Ha M L Fn.
apply: (forces_ngamma_del_ai_rev _ _ _ _ _ _ _ _ _ L)=>//.
- move=>n b E; rewrite /nf2form -/nf2form. (* TODO nicer way to refold *)
  apply/forces_imp_t=>//; apply/Fn/(In_Work _ _ _ _ _ n).
  by rewrite onth_cat (onth_size E).
by apply/forces_ngamma_cat_work_tail/Fn.
Qed.

Lemma forces_ngamma_shift_work_ai_strength i bs work ds ni ai a k :
  invariant a ->
  invariant ai ->
  Is_Monotone_kripke_tree k ->
  lookup ai i = Some bs ->
  forces_ngamma work ds ni ai (update_atoms i a).1 k ->
  forces_ngamma (bs ++ work) ds ni (delete i ai).1 (update_atoms i a).1 k.
Proof.
move=>Ha Hai M L Fn.
apply: forces_ngamma_cat_work.
- move=>n b E; apply: (forces_imp_app_t _ (Atom i)).
  - rewrite (_ : Atom i = nf2form (NAtom i)) //; apply: Fn.
    by apply: (in_ngamma_ins_a_head _ _ _ _ _ a).
  rewrite (_ : Imp (Atom i) (nf2form b) = nf2form (AImp i b )) //; apply: Fn.
  by apply/In_Atomic_Imps/E.
by apply: forces_ngamma_del_ai.
Qed.

End Forces_NGamma.
