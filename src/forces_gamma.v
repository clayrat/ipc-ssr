From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq order.
From ipcssr Require Import forms normal_forms kripke_trees in_gamma.

Section Forces_NGamma.
Context {disp : unit} {A : orderType disp}.

Definition forces_gamma (gamma : seq (form A)) (work : seq (normal_form A))
                        (k : kripke_tree A) : Prop :=
  forall a, in_gamma gamma work a -> forces_t k a.

Lemma forces_gamma_cons_gamma gamma work k a :
  forces_t k a -> forces_gamma gamma work k ->
  forces_gamma (a :: gamma) work k.
Proof.
rewrite /forces_gamma=>Fa Fg c.
case/in_gamma_cons_gamma_rev=>[|->] //.
by apply: Fg.
Qed.

Lemma forces_gamma_cons_gamma_tail gamma work k a :
  forces_gamma (a :: gamma) work k -> forces_gamma gamma work k.
Proof.
rewrite /forces_gamma=>Fa c H.
by apply/Fa/in_gamma_cons_gamma_tail.
Qed.

Lemma forces_gamma_cons_gamma_head gamma work k a :
  forces_gamma (a :: gamma) work k -> forces_t k a.
Proof. by apply; apply/in_gamma_cons_gamma_head. Qed.

(*********************************************************************)

(* TODO bijection? *)
Lemma forces_gamma_shift_gamma_work a gamma work k :
  forces_gamma (nf2form a :: gamma) work k -> forces_gamma gamma (a :: work) k.
Proof.
rewrite /forces_gamma=>Fa c H.
by apply/Fa/in_gamma_shift_work_gamma.
Qed.

Lemma forces_gamma_shift_work_gamma a gamma work k :
  forces_gamma gamma (a :: work) k -> forces_gamma (nf2form a :: gamma) work k.
Proof.
rewrite /forces_gamma=>Fa c H.
by apply/Fa/in_gamma_shift_gamma_work.
Qed.

(*********************************************************************)

Lemma forces_gamma_cons_gamma_weak gamma work k a b :
  (forces_t k a -> forces_t k b) ->
  forces_gamma (a :: gamma) work k -> forces_gamma (b :: gamma) work k.
Proof.
move=>Fab Fa.
apply/forces_gamma_cons_gamma.
- by apply/Fab/forces_gamma_cons_gamma_head/Fa.
by apply/forces_gamma_cons_gamma_tail/Fa.
Qed.

Lemma forces_gamma_cons_gamma_weak2 gamma work k a b c :
  (forces_t k a -> forces_t k b -> forces_t k c) ->
  forces_gamma (a :: b :: gamma) work k -> forces_gamma (c :: gamma) work k.
Proof.
move=>Fabc Fab.
apply/forces_gamma_cons_gamma.
- apply/Fabc; apply/forces_gamma_cons_gamma_head; first by exact: Fab.
  by apply/forces_gamma_cons_gamma_tail/Fab.
by apply/forces_gamma_cons_gamma_tail/forces_gamma_cons_gamma_tail/Fab.
Qed.

End Forces_NGamma.
