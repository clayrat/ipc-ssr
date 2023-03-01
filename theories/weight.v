From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq (*bigop*).
From ipcssr Require Import (*prelude*) forms.

Section Weight.
Context {A : Type}.

Fixpoint weight (a : form A) : nat :=
  match a with
  | Falsum => 1
  | Atom _ => 1
  | AndF a b => (weight a + weight b).+1
  | OrF Falsum b => (weight b).+1
  | OrF (Atom _) b => (weight b).+1
  | OrF a b => (weight b + weight a).+2
  | Imp a b => weight_neg a + weight b
  end
with weight_neg (a : form A) : nat :=
  match a with
  | Falsum => 0
  | Atom _ => 0
  | AndF a b => (weight_neg a + weight_neg b).+1
  | OrF a b => (weight_neg a + weight_neg b).+3
  | Imp Falsum b => 1
  | Imp (Atom _) Falsum => 2
  | Imp (Atom _) (Atom _) => 1
  | Imp (Atom _) b => (weight_neg b).+3
  | Imp a b => (weight_neg b + weight a).+4
  end.

Fixpoint weight_goal (a : form A) : nat :=
  match a with
  | Falsum => 0
  | Atom _ => 0
  | AndF _ _ => 1
  | OrF _ _ => 1
  | Imp _ b => (weight_goal b).+1
  end.

Definition weight_gamma :=
  foldr (fun a n => weight a + n) 0.

(*
Lemma weight_gammaE l :
  weight_gamma l = \sum_(i <- l) weight i.
Proof. by rewrite /weight_gamma -fusion_map foldrE big_map. Qed.
*)

(**********************************************************************)

Lemma weight_ge_1 a : 0 < weight a.
Proof.
elim: a=>//=; first by case.
move=>f1 H1 f2 H2.
by apply: ltn_addl.
Qed.

Lemma weight_neg_le j a :
 weight_neg (Imp (Atom j) a) <= (weight_neg a).+3.
Proof. by case: a. Qed.

Lemma weight_vimp l a : weight (vimp l a) = weight a.
Proof.
elim: l a=>//= x l IH a.
by apply: (IH (Imp (Atom x) a)).
Qed.

Lemma weight_gamma_weak a b gamma n :
  weight a < weight b ->
  weight_gamma (b :: gamma) <= n ->
  weight_gamma (a :: gamma) < n.
Proof.
move=>/= H Hb.
apply/leq_trans/Hb.
by rewrite ltn_add2r.
Qed.

Lemma weight_gamma_weak' a b gamma n :
  weight a < weight b ->
  weight b + weight_gamma gamma <= n ->
  weight a + weight_gamma gamma < n.
Proof. by apply: weight_gamma_weak. Qed.

Lemma weight_gamma_weak2 a b c gamma n :
  weight a + weight b < weight c ->
  weight_gamma (c :: gamma) <= n -> weight_gamma (a :: b :: gamma) < n.
Proof.
move=>/= H Hac.
apply/leq_trans/Hac.
by rewrite addnA ltn_add2r.
Qed.

Lemma weight_gamma_weak2' a b c gamma n :
  weight a + weight b < weight c ->
  weight c + weight_gamma gamma <= n ->
  weight a + (weight b + weight_gamma gamma) < n.
Proof. by apply: weight_gamma_weak2. Qed.

Lemma weight_gamma_weak3 a b c d gamma n :
  weight a + weight b + weight c < weight d ->
  weight_gamma (d :: gamma) <= n ->
  weight_gamma (a :: b :: c :: gamma) < n.
Proof.
move=>/= H Hd.
apply/leq_trans/Hd.
by rewrite !addnA ltn_add2r.
Qed.

Lemma weight_gamma_weak3' a b c d gamma n :
  weight a + weight b + weight c < weight d ->
  weight d + weight_gamma gamma <= n ->
  weight a + (weight b + (weight c + weight_gamma gamma)) < n.
Proof. by apply: weight_gamma_weak3. Qed.

End Weight.
