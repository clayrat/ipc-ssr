From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq path eqtype order bigop ssrAC.
From ipcssr Require Import prelude avlmap forms normal_forms in_ngamma catrev le_ks kripke_trees.

Section NWeight.
Context {A : Type}.

Fixpoint nweight (a : form A) : nat :=
  match a with
  | Atom _     => 0
  | Falsum     => 0
  | AndF a0 a1 => (nweight a0 + nweight a1).+1
  | OrF  a0 a1 => (nweight a0 + nweight a1).+1
  | Imp  a0 a1 => (nweight a0 + nweight a1).+1
  end.

(******************************************************************)


Definition nweight_work :=
  foldr (fun a n => nweight (nf2form a) + n) 0.
Definition nweight_disj (d : disj A) := nweight (disj2form d).
Definition nweight_ds :=
  foldr (fun d n => nweight_disj d + n) 0.
Definition nweight_atomicimp (a : normal_form A) := (nweight (nf2form a)).+1.
Definition nweight_bs :=
  foldr (fun b n => nweight_atomicimp b + n) 0.

Lemma nweight_workE l :
  nweight_work l = \sum_(i <- l) nweight (nf2form i).
Proof. by rewrite /nweight_work -fusion_map foldrE big_map. Qed.

Remark nweight_work_cat bs work :
  nweight_work (bs ++ work) = nweight_work bs + nweight_work work.
Proof. by rewrite !nweight_workE big_cat. Qed.

Lemma nweight_bsE l :
  nweight_bs l = \sum_(i <- l) nweight_atomicimp i.
Proof. by rewrite /nweight_bs -fusion_map foldrE big_map. Qed.

End NWeight.

Section NWeightOrd.
Context {disp : unit} {A : orderType disp}.

Definition nweight_nestedimp (x : nested_imp A) := nweight (nested_imp2form x).
Definition nweight_ni :=
  foldr (fun x n => nweight_nestedimp x + n) 0.
Definition nweight_decoratednestedimp (x : decorated_nested_imp A) :=
  nweight (nimp2form x.1).
Definition nweight_dni :=
  foldr (fun x n => nweight_decoratednestedimp x + n) 0.
Definition nweight_ai (ai : atomic_imps A) :=
  foldr_v (fun x n => nweight_bs x + n) 0 ai.

(***************************************************************************)

Lemma nweight_niE ni :
  nweight_ni ni = \sum_(i <- ni) nweight_nestedimp i.
Proof. by rewrite /nweight_ni -fusion_map foldrE big_map. Qed.

Lemma nweight_dniE dni :
  nweight_dni dni = \sum_(i <- dni) nweight_decoratednestedimp i.
Proof. by rewrite /nweight_dni -fusion_map foldrE big_map. Qed.

Lemma nweight_aiE ai :
  nweight_ai ai = \sum_(i <- inorder_kv ai) nweight_bs i.2.
Proof. by rewrite /nweight_ai foldr_inorder -fusion_map foldrE big_map. Qed.

Remark nweight_ai_ins i b ai :
  invariant ai ->
  nweight_ai (update_aimps b i ai) = nweight (nf2form (AImp i b)) + nweight_ai ai.
Proof.
case/andP=>Ha _; rewrite /nf2form -/nf2form /= add0n !nweight_aiE
  -!(big_map snd predT nweight_bs) /= -/values.
under eq_bigr do rewrite nweight_bsE.
under [X in _ = _ + X]eq_bigr do rewrite nweight_bsE.
rewrite -!big_flatten /= inorder_upsert //.
have S: sorted <%O (keys (inorder_kv ai)) by case/andP: Ha.
by rewrite (perm_big _ (perm_flatten_values_cons _ _ S)) /= big_cons.
Qed.

Remark nweight_ai_del i bs ai :
  invariant ai -> regular ai ->
  lookup ai i = Some bs ->
  (nweight_work bs + nweight_ai (delete i ai) < nweight_ai ai)%N.
Proof.
case/andP=>Ha _ R L.
rewrite nweight_workE !nweight_aiE -!(big_map snd predT nweight_bs) /= -/values.
under [X in (_ + X < _)%N]eq_bigr do rewrite nweight_bsE.
under [X in (_ < X)%N]eq_bigr do rewrite nweight_bsE.
rewrite -!big_flatten /= inorder_delete //.
have S: sorted <%O (keys (inorder_kv ai)) by case/andP: Ha.
rewrite (perm_big _ (perm_flatten_lookup_del i S)) /=.
rewrite -inorder_lookup // L /= big_cat /= {2}/nweight_atomicimp ltn_add2r.
under [X in (_ < X)%N]eq_bigr do rewrite -addn1.
rewrite big_split /= sum1_size -[X in (X < _)%N]addn0 ltn_add2l.
by move: (R i); rewrite L /= lt0n.
Qed.

(*********************************************************************)

Remark nweight_eqv_ni ni1 ni2 :
  eqv_ni ni1 ni2 -> nweight_ni ni1 = nweight_ni ni2.
Proof.
rewrite !nweight_niE /nweight_nestedimp /nested_imp2form.
rewrite -!(big_map nested_imp2nimp predT (nweight \o nimp2form)) /=.
by move/eqP=>->.
Qed.

Remark nweight_catrev dni ni :
  nweight_ni ni + nweight_dni dni = nweight_ni (catrev_d dni ni).
Proof.
rewrite !nweight_niE nweight_dniE catrev_d_eq catrevE big_cat /= [RHS]addnC.
congr (addn _); rewrite (perm_big _ (permEl (perm_rev (map _ _)))) /= big_map.
by apply: eq_bigr; case.
Qed.

(**********************************************************************)

Definition nweight_Sequent (work : seq (normal_form A)) (ds : seq (disj A))
                           (ni : seq (nested_imp A)) (ai : atomic_imps A) :=
  nweight_work work + (nweight_ds ds + (nweight_ni ni + nweight_ai ai)).

Lemma nweight_shift_work_ni0 x work ds ni ai :
  nweight_Sequent (NImp_NF x :: work) ds ni ai =
  nweight_Sequent work ds (Undecorated x :: ni) ai.
Proof.
by rewrite /nweight_Sequent /= ![LHS]addnA (ACl (2*(3*(1*4*5)))%AC).
Qed.

Lemma nweight_shift_work_ds i j work ds ni ai :
  nweight_Sequent (NDisj i j :: work) ds ni ai =
  nweight_Sequent work ((i, j) :: ds) ni ai.
Proof.
by rewrite /nweight_Sequent /= /nweight_disj /= !addn0 ![LHS]addnA (ACl (2*(1*3*(4*5)))%AC).
Qed.

Lemma nweight_shift_work_ai i b work ds ni ai :
  invariant ai ->
  nweight_Sequent (AImp i b :: work) ds ni ai =
  nweight_Sequent work ds ni (update_aimps b i ai).
Proof.
move=>Ha.
by rewrite /nweight_Sequent /= nweight_ai_ins //= -/nf2form add0n
  ![LHS]addnA (ACl (2*(3*(4*(1*5))))%AC).
Qed.

(*******************************************************************)

Lemma nweight_shift_ai_work i bs work ds ni ai :
  invariant ai -> regular ai ->
  lookup ai i = Some bs ->
  (nweight_Sequent (bs ++ work) ds ni (delete i ai) < nweight_Sequent work ds ni ai)%N.
Proof.
move=>Ha R L.
rewrite /nweight_Sequent /= nweight_work_cat !addnA
  [X in (X < _)%N](ACl ((2*3*4)*(1*5))%AC) /= ltn_add2l.
by apply: nweight_ai_del.
Qed.

(*************************************************************************)

Lemma nweight_sequent_eqv work ds ni1 ni2 ai :
  eqv_ni ni1 ni2 ->
  nweight_Sequent work ds ni1 ai = nweight_Sequent work ds ni2 ai.
Proof.
move=>E; rewrite /nweight_Sequent /= !(addnC _ ( nweight_ai _)) !addnA.
by congr (addn _); apply: nweight_eqv_ni.
Qed.

(*******************************************************************)

Lemma nweight_sequent_nimp_left a0 a1 b work ds ni1 ni2 dni1 ai :
  eqv_ni (catrev_d dni1 ni1) ni2 ->
  nweight_Sequent work ds (catrev_d dni1 (Undecorated (NImp a0 a1 b) :: ni1)) ai =
  (nweight_Sequent (AImp a1 b :: NAtom a0 :: work) ds ni2 ai).+1.
Proof.
move=> E.
rewrite /nweight_Sequent -(nweight_eqv_ni _ _ E) !rev_app_app.
rewrite !nweight_niE !big_cat /= big_cons /nweight_nestedimp /= -/nf2form !add0n -!nweight_niE.
by rewrite add1n -addn2 !addnA !addSn [LHS](ACl (4*1*2*3*6*7*5)%AC) /= addn2.
Qed.

Lemma nweight_sequent_nimp_right a0 a1 b work ds ni1 ni2 dni1 ai :
  eqv_ni (catrev_d dni1 ni1) ni2 ->
  nweight_Sequent work ds (catrev_d dni1 (Undecorated (NImp a0 a1 b) :: ni1)) ai =
  (nweight_Sequent (b :: work) ds ni2 ai).+2.
Proof.
move=> E.
rewrite /nweight_Sequent -(nweight_eqv_ni _ _ E) !rev_app_app.
rewrite !nweight_niE !big_cat /= big_cons /nweight_nestedimp /= -/nf2form !add0n -!nweight_niE.
by rewrite add1n -addn2 !addnA [LHS](ACl (4*1*2*3*6*7*5)%AC) /= addn2.
Qed.

Lemma nweight_sequent_left_disj_left i j work ds ni1 ni2 ai :
  eqv_ni ni1 ni2 ->
  nweight_Sequent work ((i, j) :: ds) ni1 ai =
  (nweight_Sequent (NAtom i :: work) ds ni2 ai).+1.
Proof.
move=> E.
rewrite /nweight_Sequent -(nweight_eqv_ni _ _ E) /=.
by rewrite /nweight_disj /= !add0n !addnA addn1 !addSn.
Qed.

Lemma nweight_sequent_left_disj_right i j work ds ni1 ni2 ai :
  eqv_ni ni1 ni2 ->
  nweight_Sequent work ((i, j) :: ds) ni1 ai =
  (nweight_Sequent (NAtom j :: work) ds ni2 ai).+1.
Proof.
move=> E.
rewrite /nweight_Sequent -(nweight_eqv_ni _ _ E) /=.
by rewrite /nweight_disj /= !add0n !addnA addn1 !addSn.
Qed.

End NWeightOrd.
