From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import kripke_trees normal_forms in_ngamma catrev le_ks.

Section Lt_Ks.
Context {disp : unit} {A : orderType disp}.

Fixpoint count_undecs (n : seq (nested_imp A)) : nat :=
  match n with
  | [::] => 0
  | Undecorated _ :: n => (count_undecs n).+1
  | Decorated _ _ :: n => count_undecs n
  end.

Lemma count_undecs_cat ni1 ni2 :
  count_undecs (ni1 ++ ni2) = count_undecs ni1 + count_undecs ni2.
Proof.
elim: ni1=>//= n ni1 IH.
by case: n=>// _; rewrite IH addSn.
Qed.

Lemma le_ni_le_count_undecs ni1 ni2 :
  le_ni ni1 ni2 -> (count_undecs ni1 <= count_undecs ni2)%N.
Proof.
elim: ni1 ni2=>// n1 ni1 IH; case=>[|n2 ni2] /=; first by case: n1.
case: n2=>[n2|n2 x2]; case: n1=>[n1|n1 x1] //.
- by case/andP=>_ /IH.
- by case/andP=>_ /IH H; apply/ltnW.
by case/and3P=>_ _ /IH.
Qed.

Lemma count_undecs_catrev dni ni :
  count_undecs (catrev_d dni ni) = count_undecs ni.
Proof.
rewrite rev_app_app count_undecs_cat addnC -[RHS]addn0.
congr (addn _); elim: dni=>//=d dni IH.
rewrite rev_d_eq /= rev_cons -rev_d_eq -cats1 count_undecs_cat {}IH add0n.
by case: d.
Qed.

Lemma le_ks_le_count_undecs ni1 dni1 ni2 dni2 :
  le_ni (catrev_d dni1 ni1) (catrev_d dni2 ni2) ->
  (count_undecs ni1 <= count_undecs ni2)%N.
Proof. by move/le_ni_le_count_undecs; rewrite !count_undecs_catrev. Qed.

Definition lt_ks ni1 dni1 ni2 dni2 : Type :=
  le_ni (catrev_d dni1 ni1) (catrev_d dni2 ni2) *
  ({count_undecs ni1 < count_undecs ni2} + {size ni1 < size ni2})%N.

Lemma lt_ks_rec (P : seq (nested_imp A) -> Type) :
 (forall ni2 dni2,
  (forall ni1 dni1, lt_ks ni1 dni1 ni2 dni2 -> P (catrev_d dni1 ni1)) -> P (catrev_d dni2 ni2)) ->
  forall ni, P ni.
Proof.
move=>step ni0.
suff claim n m ni dni : (count_undecs ni < n)%N -> (size ni < m)%N -> P (catrev_d dni ni).
- by apply: (claim (count_undecs ni0).+1 (size ni0).+1 ni0 [::]).
elim: n m ni dni=>// n IHn; elim=>// m IHm ni dni; rewrite !ltnS => Lc Ls.
apply: step=>ni1 dni1; case=>L; case=>H.
- apply: (IHn (size ni1).+1)=>//.
  by apply/leq_trans/Lc.
apply: IHm.
- by rewrite ltnS; apply/leq_trans/Lc/le_ks_le_count_undecs/L.
by apply/leq_trans/Ls.
Qed.

Lemma lt_ks_shift_nd ni ni1 dni dni1 x k :
  le_ni (catrev_d dni1 ni1) (catrev_d ((x, k) :: dni) ni) ->
  lt_ks ni1 dni1 (Undecorated x :: ni) dni.
Proof.
move=>L; rewrite /lt_ks /= !ltnS; split.
- move: L; rewrite (rev_app_app dni) (rev_app_app (_::dni))
   rev_d_eq /= rev_cons -rev_d_eq -cats1 -catA /= => L.
  apply/(le_ni_trans _ _ _ L)/le_ni_app_dn=>//.
  by exact: le_ni_refl.
by left; apply/le_ks_le_count_undecs/L.
Qed.

Lemma lt_ks_shift_dd ni dni x k :
  lt_ks ni ((x, k) :: dni) (Decorated x k :: ni) dni.
Proof.
split=>/=; last by right.
by apply: le_ni_refl.
Qed.

End Lt_Ks.
