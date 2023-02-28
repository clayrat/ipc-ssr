From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq order.
From ipcssr Require Import avlmap kripke_trees in_ngamma.

Section Disjunct.
Context {disp : unit} {A : orderType disp}.

Definition a_ai_disj (a : atoms A) (ai : atomic_imps A) : Prop :=
  forall i, lookup a i -> ~~ lookup ai i.

Definition a_goal_disj (a : atoms A) (goal : A) : Prop :=
  ~~ lookup a goal.

Lemma disjs_insert_ai i b a ai :
  invariant ai ->
  a_ai_disj a ai -> ~~ lookup a i ->
  a_ai_disj a (update_aimps b i ai).1.
Proof.
rewrite /a_ai_disj=>Ha Hd Hi j Hj.
rewrite lookup_upsert //=; case: eqP=>[E|_].
- by rewrite -E Hj in Hi.
by apply: Hd.
Qed.

Lemma disjs_delete_ai i a ai :
  invariant a -> invariant ai ->
  a_ai_disj a ai ->
  a_ai_disj (update_atoms i a).1 (delete i ai).1.
Proof.
rewrite /a_ai_disj =>Ha Hai Hd j.
rewrite lookup_upsert // lookup_delete //=; case: eqP=>//= _.
by apply: Hd.
Qed.

Lemma goal_disj_insert_a i goal a :
  invariant a ->
  a_goal_disj a goal -> goal != i ->
  a_goal_disj (update_atoms i a).1 goal.
Proof.
rewrite /a_goal_disj =>Ha Hd N.
by rewrite lookup_upsert //= (negbTE N).
Qed.

Lemma disjs_insert_a i a ai :
  invariant a ->
  a_ai_disj a ai -> ~~ lookup ai i -> (* could also be positive: lookup a i *)
  a_ai_disj (update_atoms i a).1 ai.
Proof.
rewrite /a_ai_disj =>Ha Hd N j.
rewrite lookup_upsert //=; case: eqP=>[{j}->|_ ] //.
by apply: Hd.
Qed.

End Disjunct.
