From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq.
From ipcssr Require Import forms normal_forms derivations in_gamma derivable_def.

Section Sound.
Context {A : Type}.

Definition sound (gamma : seq (form A)) (work : seq (normal_form A)) (ctx : seq (form A)) :=
  forall a, in_gamma gamma work a -> Derivable ctx a.

Lemma sound_cons_gamma gamma work ctx a :
  Derivable ctx a ->
  sound gamma work ctx -> sound (a :: gamma) work ctx.
Proof.
rewrite /sound =>D S c.
case/in_gamma_cons_gamma_rev=>[|{c}->] //.
by apply: S.
Qed.

Lemma sound_cons_gamma_tail gamma work ctx a :
  sound (a :: gamma) work ctx -> sound gamma work ctx.
Proof.
rewrite /sound =>S c D.
by apply/S/in_gamma_cons_gamma_tail.
Qed.

Lemma sound_cons_gamma_head gamma work ctx a :
  sound (a :: gamma) work ctx -> Derivable ctx a.
Proof. by apply; exact: in_gamma_cons_gamma_head. Qed.

(**********************************************************************)

(* TODO bijection? *)
Lemma sound_shift_gamma_work a gamma work ctx :
  sound (nf2form a :: gamma) work ctx -> sound gamma (a :: work) ctx.
Proof.
rewrite /sound =>S c D.
by apply/S/in_gamma_shift_work_gamma.
Qed.

Lemma sound_shift_work_gamma a gamma work ctx :
  sound gamma (a :: work) ctx -> sound (nf2form a :: gamma) work ctx.
Proof.
rewrite /sound =>S c D.
by apply/S/in_gamma_shift_gamma_work.
Qed.

(**********************************************************************)

Lemma sound_cons_gamma_cons_ctx gamma work ctx a :
  sound gamma work ctx -> sound (a :: gamma) work (a :: ctx).
Proof.
move=>S; apply: sound_cons_gamma.
- by apply/(Derivable_Intro _ _ (Var 0))/ByAssumption.
rewrite /sound =>c /S [t Dt].
by apply/(Derivable_Intro _ _ (Shift t))/ShiftIntro.
Qed.

(************************************************************)

Lemma sound_cons_gamma_weak gamma work ctx a b :
  (Derivable ctx a -> Derivable ctx b) ->
  sound (a :: gamma) work ctx -> sound (b :: gamma) work ctx.
Proof.
move=>Dab S; apply: sound_cons_gamma.
- by apply/Dab/sound_cons_gamma_head/S.
by apply/sound_cons_gamma_tail/S.
Qed.

Lemma sound_cons_gamma_weak2 gamma work ctx a b c :
  (Derivable ctx a -> Derivable2 ctx b c) ->
  sound (a :: gamma) work ctx -> sound (b :: c :: gamma) work ctx.
Proof.
move=>Dabc S; case: Dabc.
- by apply/sound_cons_gamma_head/S.
move=>Db Dc; do 2!apply: sound_cons_gamma=>//.
by apply/sound_cons_gamma_tail/S.
Qed.

End Sound.
