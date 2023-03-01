From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import forms normal_forms derivations kripke_trees in_gamma forces_gamma derivable_def.

Section Minimal.
Context {disp : unit} {A : orderType disp}.

Definition minimal (gamma : seq (form A)) (work : seq (normal_form A))
                   (ctx : seq (form A)) : Prop :=
  forall k, Is_Monotone_kripke_tree k ->
  forces_gamma gamma work k -> {in ctx, forall a, forces_t k a}.

Lemma minimal_derivable_forces gamma work ctx k :
  Is_Monotone_kripke_tree k ->
  forces_gamma gamma work k ->
  minimal gamma work ctx ->
  forall a, Derivable ctx a -> forces_t k a.
Proof.
move=>Mk F M a; case=>t D.
apply/(soundness_t ctx t)=>//.
by apply: M.
Qed.

(*************************************************************************)

(* TODO bijection? *)
Lemma minimal_shift_gamma_work a gamma work ctx :
  minimal (nf2form a :: gamma) work ctx ->
  minimal gamma (a :: work) ctx.
Proof.
rewrite /minimal => /= M k Mk F f I.
by apply: M=>//; apply: forces_gamma_shift_work_gamma.
Qed.

Lemma minimal_shift_work_gamma a gamma work ctx :
  minimal gamma (a :: work) ctx ->
  minimal (nf2form a :: gamma) work ctx.
Proof.
rewrite /minimal=>/= M k Mk F f I.
by apply: M=>//; apply: forces_gamma_shift_gamma_work.
Qed.

(*************************************************************************)

Lemma minimal_cons_gamma_cons_ctx gamma work ctx a :
  minimal gamma work ctx -> minimal (a :: gamma) work (a :: ctx).
Proof.
rewrite /minimal=>/= M k Mk F f.
rewrite inE; case/orP=>[/eqP{f}->|I].
- by apply/F/in_gamma_cons_gamma_head.
by apply: M=>//; apply/forces_gamma_cons_gamma_tail/F.
Qed.

(*************************************************************************)

Lemma minimal_cons_gamma_weak gamma work ctx a b :
  (forall k, Is_Monotone_kripke_tree k ->
    forces_t k b -> forces_t k a) ->
  minimal (a :: gamma) work ctx -> minimal (b :: gamma) work ctx.
Proof.
rewrite /minimal=>/= H M k Mk F f I.
apply: M=>//; apply: (forces_gamma_cons_gamma_weak _ _ _ b)=>//.
by apply: H.
Qed.

Lemma minimal_cons_gamma_weak2 gamma work ctx a b c :
  (forall k, Is_Monotone_kripke_tree k ->
    forces_t k b -> forces_t k c -> forces_t k a) ->
  minimal (a :: gamma) work ctx -> minimal (b :: c :: gamma) work ctx.
Proof.
rewrite /minimal=>/= H M k Mk F f I.
apply: M=>//; apply: (forces_gamma_cons_gamma_weak2 _ _ _ b c)=>//.
by apply: H.
Qed.

End Minimal.
