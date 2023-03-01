From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq eqtype order.
From ipcssr Require Import avlmap forms normal_forms kripke_trees in_ngamma forces_ngamma le_ks.

Section NDecoSound.
Context {disp : unit} {A : orderType disp}.

Definition k_deco_sound (k : kripke_tree A) (i0 i1 : A)
                        (work : seq (normal_form A)) (ds : seq (disj A))
                        (ni : seq (nested_imp A)) (ai : atomic_imps A)
                        (a : atoms A) : Prop :=
  [/\ Is_Monotone_kripke_tree k,
      forces_ngamma work ds ni ai a k &
      ~ forces_t k (Imp (Atom i0) (Atom i1))].

Definition deco_sound (work : seq (normal_form A)) (ds : seq (disj A))
                      (ni : seq (nested_imp A)) (ai : atomic_imps A)
                      (a : atoms A) : Prop :=
  forall k i0 i1 b, Decorated (NImp i0 i1 b) k \in ni ->
  k_deco_sound k i0 i1 work ds ni ai a.

(*****************************************************************)

Lemma deco_sound_cons_work_tail c work ds ni ai a :
  deco_sound (c :: work) ds ni ai a -> deco_sound work ds ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: (forces_ngamma_cons_work_tail c).
Qed.

Lemma deco_sound_cons_ds_tail work i j ds ni ai a :
  deco_sound work ((i, j) :: ds) ni ai a -> deco_sound work ds ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: (forces_ngamma_cons_ds_tail _ i j).
Qed.

Lemma deco_sound_cons_ni_tail work ds x ni ai a :
  deco_sound work ds (x :: ni) ai a -> deco_sound work ds ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C k i0 i1 b); first by rewrite inE D orbT.
move=>{C D}M F NF; split=>//.
by apply: (forces_ngamma_cons_ni_tail _ _ x).
Qed.

(*****************************************************************)

(* TODO roll into bijections? *)

Lemma deco_sound_shift_ds_work work i j ds ni ai a :
  deco_sound work ((i, j) :: ds) ni ai a ->
  deco_sound (NDisj i j :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_ds_work.
Qed.

Lemma deco_sound_shift_work_ds i j work ds ni ai a :
  deco_sound (NDisj i j :: work) ds ni ai a ->
  deco_sound work ((i, j) :: ds) ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_ds.
Qed.

Lemma deco_sound_shift_ni_work x work ds ni ai a :
  deco_sound work ds (x :: ni) ai a ->
  deco_sound (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b D.
case: (C k i0 i1 b); first by rewrite inE D orbT.
move=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_ni_work.
Qed.

Lemma deco_sound_shift_work_ni0 x work ds ni ai a :
  deco_sound (NImp_NF x :: work) ds ni ai a ->
  deco_sound work ds (Undecorated x :: ni) ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 b; rewrite inE /= => D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_ni.
Qed.

(* new + old *)
Lemma deco_sound_shift_ai_work i b work ds ni ai a :
  invariant ai ->
  deco_sound work ds ni (update_aimps b i ai).1 a ->
  deco_sound (AImp i b :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>Ha C k i0 i1 c D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_ai_work.
Qed.

Lemma deco_sound_shift_work_ai i b work ds ni ai a :
  invariant ai ->
  deco_sound (AImp i b :: work) ds ni ai a ->
  deco_sound work ds ni (update_aimps b i ai).1 a.
Proof.
rewrite /deco_sound=>Ha C k i0 i1 c D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_ai.
Qed.

Lemma deco_sound_shift_a_work i work ds ni ai a :
  invariant a ->
  deco_sound work ds ni ai (update_atoms i a).1 ->
  deco_sound (NAtom i :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>Ha C k i0 i1 c D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_a_work.
Qed.

Lemma deco_sound_shift_work_a i work ds ni ai a :
  invariant a ->
  deco_sound (NAtom i :: work) ds ni ai a ->
  deco_sound work ds ni ai (update_atoms i a).1.
Proof.
rewrite /deco_sound=>Ha C k i0 i1 c D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_a.
Qed.

Lemma deco_sound_shift_ni_x_ni_work x work ds ni1 ni2 ai a :
  deco_sound work ds (ni1 ++ x :: ni2) ai a ->
  deco_sound (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 c D.
case: (C k i0 i1 c).
- by rewrite mem_cat inE orbCA -mem_cat D orbT.
move=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_ni_x_ni_work.
Qed.

Lemma deco_sound_shift_work_ninni x work ds ni1 ni2 ai a :
  deco_sound (NImp_NF x :: work) ds (ni1 ++ ni2) ai a ->
  deco_sound work ds (ni1 ++ Undecorated x :: ni2) ai a.
Proof.
rewrite /deco_sound=>C k i0 i1 c; rewrite mem_cat inE /= -mem_cat => D.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_ni_x_ni.
Qed.

Lemma deco_sound_shift_work_nirni a0 a1 b k1 work ds ni1 ni2 ai a :
  k_deco_sound k1 a0 a1 work ds (ni1 ++ Decorated (NImp a0 a1 b) k1 :: ni2) ai a ->
  deco_sound (NImp_NF (NImp a0 a1 b) :: work) ds (ni1 ++ ni2) ai a ->
  deco_sound work ds (ni1 ++ Decorated (NImp a0 a1 b) k1 :: ni2) ai a.
Proof.
rewrite /deco_sound=>K C k i0 i1 c; rewrite mem_cat inE orbCA -mem_cat.
case/orP=>[/eqP[->-> _ ->]|D] //.
case: (C _ _ _ _ D)=>{C D}M F NF; split=>//.
by apply: forces_ngamma_shift_work_ni_x_ni.
Qed.

(********************************************************************)

Lemma deco_sound_le work ds ni1 ni2 ai a :
  le_ni ni1 ni2 -> deco_sound work ds ni1 ai a ->
  deco_sound work ds ni2 ai a.
Proof.
rewrite /deco_sound=>L C k i0 i1 c D.
case: (C k i0 i1 c); first by apply/in_k_le/D.
move=>{C D}M F NF; split=>//.
apply/forces_ngamma_eqv/F.
by apply: ge_eqv.
Qed.

(*********************************************************************)

Lemma deco_sound_cons_work_weak b c work ds ni ai a :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_t k (nf2form b) -> forces_t k (nf2form c)) ->
  deco_sound (b :: work) ds ni ai a -> deco_sound (c :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>H C k i0 i1 d D.
case: (C _ _ _ _ D)=>{d C D}M F NF; split=>//.
apply: (forces_ngamma_cons_work_weak b)=>//.
by apply: H.
Qed.

Lemma deco_sound_cons_work_weak2 b c d work ds ni ai a :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_t k (nf2form b) -> forces_t k (nf2form c) -> forces_t k (nf2form d)) ->
  deco_sound (b :: c :: work) ds ni ai a ->
  deco_sound (d :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>H C k i0 i1 e D.
case: (C _ _ _ _ D)=>{e C D}M F NF; split=>//.
apply: (forces_ngamma_cons_work_weak2 b c)=>//.
by apply: H.
Qed.

Lemma deco_sound_cons_work_strength b c work ds ni ai a :
  (forall k, Is_Monotone_kripke_tree k ->
   forces_ngamma (b :: work) ds ni ai a k -> forces_t k (nf2form c)) ->
  deco_sound (b :: work) ds ni ai a -> deco_sound (c :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>H C k i0 i1 d D.
case: (C _ _ _ _ D)=>{d C D}M F NF; split=>//.
apply: (forces_ngamma_cons_work_weak b)=>// _.
by apply: H.
Qed.

Lemma deco_sound_shift_work_ai_weak i bs work ds ni ai a :
  invariant ai -> lookup ai i = Some bs ->
  deco_sound (bs ++ work) ds ni (delete i ai).1 a ->
  deco_sound work ds ni ai a.
Proof.
rewrite /deco_sound=>Ha L C k i0 i1 d D.
case: (C _ _ _ _ D)=>{d C D}M F NF; split=>//.
by apply: (forces_ngamma_shift_work_ai_weak i bs).
Qed.

Lemma deco_sound_shift_work_ai_strength i bs work ds ni ai a :
  invariant ai -> invariant a ->
  lookup ai i = Some bs ->
  deco_sound work ds ni ai (update_atoms i a).1 ->
  deco_sound (bs ++ work) ds ni (delete i ai).1 (update_atoms i a).1.
Proof.
rewrite /deco_sound=>Hai Ha L C k i0 i1 d D.
case: (C _ _ _ _ D)=>{d C D}M F NF; split=>//.
by apply: (forces_ngamma_shift_work_ai_strength i).
Qed.

Lemma deco_sound_inf work ds ni ni1 ni2 ai a :
  le_ni ni ni1 -> eqv_ni ni ni2 ->
  (forall x k,
    Decorated x k \in ni -> (Decorated x k \in ni1) || (Decorated x k \in ni2)) ->
  deco_sound work ds ni1 ai a -> deco_sound work ds ni2 ai a ->
  deco_sound work ds ni ai a.
Proof.
rewrite /deco_sound=>L E H C1 C2 k i0 i1 d D.
case/orP: (H _ _ D)=>{}D.
- case: (C1 _ _ _ _ D)=>{D}M F NF; split=>//.
  by apply/forces_ngamma_eqv/F/le_eqv.
case: (C2 _ _ _ _ D)=>{D}M F NF; split=>//.
by apply/forces_ngamma_eqv/F.
Qed.

Lemma deco_sound_filter_deco i work ds ni ai a :
  (forall x k, Decorated x k \in ni -> forces_t k (Atom i)) ->
  deco_sound work ds ni ai a -> deco_sound (NAtom i :: work) ds ni ai a.
Proof.
rewrite /deco_sound=>H C k i0 i1 d D.
case: (C _ _ _ _ D)=>M F NF; split=>//.
apply: forces_ngamma_cons_work=>//.
by apply/H/D.
Qed.

End NDecoSound.
