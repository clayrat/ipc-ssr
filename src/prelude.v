From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* inspect idiom so we can expand let-bound vars in proofs *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a erefl.

Notation "x 'eqn:' p" := (exist _ x p) (only parsing, at level 20).

Lemma bool_eq_iff (a b : bool) : (a <-> b) <-> a == b.
Proof.
case: a; case: b=>//; split=>//.
- by case=>/(_ isT).
by case=>_ /(_ isT).
Qed.

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.
Inductive and7 (P1 P2 P3 P4 P5 P6 P7 : Prop) : Prop :=
  And7 of P1 & P2 & P3 & P4 & P5 & P6 & P7.
Inductive and8 (P1 P2 P3 P4 P5 P6 P7 P8 : Prop) : Prop :=
  And8 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8.
Inductive and9 (P1 P2 P3 P4 P5 P6 P7 P8 P9 : Prop) : Prop :=
  And9 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9.
Inductive and10 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 : Prop) : Prop :=
  And10 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10.
Inductive and11 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 : Prop) : Prop :=
  And11 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11.
Inductive and12 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 : Prop) : Prop :=
  And12 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12.
Inductive and13 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 : Prop) : Prop :=
  And13 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13.
Inductive and14 (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 : Prop) : Prop :=
  And14 of P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 & P7 ]" := (and7 P1 P2 P3 P4 P5 P6 P7) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 & P8 ]" := (and8 P1 P2 P3 P4 P5 P6 P7 P8) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 & P9 ]" := (and9 P1 P2 P3 P4 P5 P6 P7 P8 P9) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 & P10 ]" := (and10 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 & P11 ]" :=
  (and11 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 & P12 ]" :=
  (and12 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 , P12 & P13 ]" :=
  (and13 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13) : type_scope.
Notation "[ /\ P1 , P2 , P3 , P4 , P5 , P6 , P7 , P8 , P9 , P10 , P11 , P12 , P13 & P14 ]" :=
  (and14 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14) : type_scope.

Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and7P : reflect [/\ b1, b2, b3, b4, b5, b6 & b7] [&& b1, b2, b3, b4, b5, b6 & b7].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and8P : reflect [/\ b1, b2, b3, b4, b5, b6, b7 & b8] [&& b1, b2, b3, b4, b5, b6, b7 & b8].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and9P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8 & b9] [&& b1, b2, b3, b4, b5, b6, b7, b8 & b9].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and10P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10] [&& b1, b2, b3, b4, b5, b6, b7, b8, b9 & b10].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and11P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10 & b11].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and12P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11 & b12].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and13P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12 & b13]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12 & b13].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
case: b13=>/=; last by constructor; case.
by constructor.
Qed.

Lemma and14P : reflect [/\ b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 & b14]
                       [&& b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13 & b14].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
case: b7=>/=; last by constructor; case.
case: b8=>/=; last by constructor; case.
case: b9=>/=; last by constructor; case.
case: b10=>/=; last by constructor; case.
case: b11=>/=; last by constructor; case.
case: b12=>/=; last by constructor; case.
case: b13=>/=; last by constructor; case.
case: b14=>/=; last by constructor; case.
by constructor.
Qed.

End ReflectConnectives.

Section Bool.

Lemma implyb_trans : transitive implb.
Proof. by case; case. Qed.

End Bool.

Section Arith.

Lemma uphalf_addn n m :
  uphalf n + uphalf m = odd n && odd m + uphalf (n + m).
Proof.
rewrite !uphalf_half halfD oddD.
by case: (odd n); case: (odd m)=>//=; rewrite addnCA.
Qed.

Lemma half_le n : n./2 <= n.
Proof.
elim: n=>//= n IH; rewrite uphalf_half -addn1 (addnC _ 1).
by apply: leq_add=>//; apply: leq_b1.
Qed.

Lemma uphalf_le n : uphalf n <= n.
Proof. by case: n=>//= n; rewrite ltnS; apply: half_le. Qed.

Lemma half_lt n : 0 < n -> n./2 < n.
Proof.
case: n=>// n _; rewrite -(addn1 n) halfD andbT addn0 -uphalf_half addn1.
apply/leq_ltn_trans/ltnSn.
by exact: uphalf_le.
Qed.

Lemma half_uphalfK n : n = n./2 + uphalf n.
Proof. by rewrite uphalf_half addnCA addnn odd_double_half. Qed.

Lemma half_subn n : n - n./2 = uphalf n.
Proof. by rewrite {1}(half_uphalfK n) -addnBAC // subnn. Qed.

Lemma odd2 n : odd n = odd n.+2.
Proof. by rewrite -addn2 oddD addbF. Qed.

Lemma leq_ltn_add m1 m2 n1 n2 : m1 <= n1 -> m2 < n2 -> m1 + m2 < n1 + n2.
Proof.
by move=>H1 H2; apply: (leq_ltn_trans (n:=n1 + m2)); rewrite ?ltn_add2l ?leq_add2r.
Qed.

Lemma maxn_eq0 m n : (maxn m n == 0) = (m == 0) && (n == 0).
Proof. by rewrite maxnE addn_eq0; case: m=>//=; rewrite subn0. Qed.

Lemma leq_max2l m n p : m <= n -> maxn p m <= maxn p n.
Proof. by move=>H; rewrite !maxnE leq_add2l; apply: leq_sub2r. Qed.

Lemma leq_max2r m n p : m <= n -> maxn m p <= maxn n p.
Proof. by move=>H; rewrite maxnC (maxnC n); apply: leq_max2l. Qed.

Lemma maxn_addl n m : maxn (n + m) n = n + m.
Proof. by apply/maxn_idPl/leq_addr. Qed.

Lemma maxn_addr n m : maxn n (n + m) = n + m.
Proof. by apply/maxn_idPr/leq_addr. Qed.

Lemma maxn_expn k n m : 0 < k -> maxn (k^n) (k^m) = k ^ maxn n m.
Proof.
case: k=>//; case=>[|k _]; first by rewrite !exp1n.
rewrite /maxn; case: (ltnP n m).
- by rewrite ltn_exp2l // =>->.
by rewrite ltnNge leq_exp2l // =>->.
Qed.

End Arith.

Section Mem.
Context {A : eqType}.

Lemma all_notin (p : pred A) xs y :
  all p xs -> ~~ p y -> y \notin xs.
Proof. by move/allP=>Ha; apply/contra/Ha. Qed.

Lemma all_subset (p : pred A) xs ys : {subset xs <= ys} -> all p ys -> all p xs.
Proof.
move=>H /allP Hys.
by apply/allP=>z Hz; apply/Hys/H.
Qed.

End Mem.

Section Sorted.
Variable (T : Type) (leT : rel T).
Hypothesis (leT_tr : transitive leT).

Lemma path_all (xs : seq T) x :
        path leT x xs -> all (leT x) xs.
Proof. by rewrite path_sortedE; [case/andP | exact: leT_tr]. Qed.

Lemma sorted_rconsE (xs : seq T) x :
  sorted leT (rcons xs x) = all (leT^~ x) xs && sorted leT xs.
Proof.
rewrite -(revK (rcons _ _)) rev_rcons rev_sorted /= path_sortedE; last first.
- by move=>a b c Hab /leT_tr; apply.
by rewrite all_rev rev_sorted.
Qed.

Corollary sorted_rcons (xs : seq T) x :
  sorted leT xs -> all (leT^~ x) xs -> sorted leT (rcons xs x).
Proof. by rewrite sorted_rconsE=>->->. Qed.

Lemma sorted_cat_cons_cat (l r : seq T) x :
  sorted leT (l ++ x :: r) = sorted leT (l ++ [::x]) && sorted leT (x::r).
Proof.
apply/eqP/bool_eq_iff; split.
- by move/[dup]/cat_sorted2=>->; rewrite -cat1s catA =>/cat_sorted2 ->.
case/andP=>/= + H; rewrite cats1.
case: l=>//=a l; rewrite rcons_path=>/andP [H1 H2].
by rewrite cat_path /= H1 H2.
Qed.

End Sorted.

Section SortedEq.
Variable (T : eqType) (ltT : rel T).

Lemma path_notin (xs : seq T) x :
  transitive ltT -> irreflexive ltT ->
  path ltT x xs -> x \notin xs.
Proof. by move=>Ht Hi H; apply: all_notin; [apply: (path_all Ht H) | rewrite Hi]. Qed.

End SortedEq.

Section AllProp.
Context {A : Type}.

Definition all_prop (P : A -> Prop) (l : seq A) :=
  foldr (fun t => and (P t)) True l.

Definition all_type (P : A -> Type) (l : seq A) :=
  foldr (fun t => prod (P t)) True l.

End AllProp.

Section AllPropEq.
Context {A : eqType}.

Lemma all_prop_mem (P : A -> Prop) l x :
  all_prop P l -> x \in l -> P x.
Proof.
elim: l=>//= h t IH [Ph H].
rewrite inE; case/orP=>[/eqP->|Hx] //.
by apply: IH.
Qed.

End AllPropEq.

Arguments all_prop_mem [A P l x].