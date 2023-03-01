From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq order.
From ipcssr Require Import prelude avlmap forms normal_forms derivations kripke_trees
                           in_ngamma forces_ngamma derivable_def
                           in_gamma forces_gamma
                           nsearch sound minimal weight rules.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Search.
Context {A : Type}.

Definition vlist : Type := seq (seq A * form A).

Fixpoint vlist2list (gamma : vlist) : seq (form A) :=
  if gamma is (l, a) :: gamma
    then vimp l a :: vlist2list gamma else [::].

Fixpoint vlist2hlist (gamma : vlist) : seq (form A) :=
  if gamma is (_, a) :: gamma
    then a :: vlist2hlist gamma else [::].

Fixpoint list2vlist (gamma : seq (form A)) : vlist :=
  if gamma is a :: gamma
    then ([::], a) :: list2vlist gamma else [::].

Lemma vlist_eq gamma : gamma = vlist2list (list2vlist gamma).
Proof. by elim: gamma=>//= a gamma {1}->. Qed.

End Search.

Section SearchOrd.
Context {disp : unit} {A : orderType disp}.

Definition search_atom_invariant (n : nat) :=
  forall (goal : A) (gamma : vlist) (work : seq (normal_form A))
         (ctx : seq (form A)) (j : A),
  (weight_gamma (vlist2hlist gamma) < n)%N ->
  csearch_spec (Atom goal) (vlist2list gamma) work ctx j.

Variant search_spec (goal : form A) (gamma : seq (form A)) : Type :=
  | Sderivable of Derivable gamma goal
  | Srefutable k of
      Is_Monotone_kripke_tree k &
      {in gamma, forall a, forces_t k a} &
      ~ forces_t k goal.

End SearchOrd.

(* TODO ssrnum? *)
Section SearchNat.

Lemma search_atom_aux n : search_atom_invariant (A:=[orderType of nat]) n.
Proof.
rewrite /search_atom_invariant /=; elim: n=>// n IH goal.
(* 0 < n *)
case=>/= [|a gamma] work ctx j.
- (* gamma = [::] *)
  rewrite /search_spec=>_ /= Hg _ Hc S M.
  case: (nsearch goal work ctx)=>/=.
  - move=>m a E.
    by apply/S/In_Work1/E.
  - move=>k Mk Fk.
    apply: M=>//; rewrite /forces_gamma=>c.
    case=>{c} //= m a E.
    by apply/Fk/onth_mem/E.
  - apply: derivable.
  move=>k Mk Fk Nk.
  apply: (refutable _ _ _ _ k)=>//.
  rewrite /forces_gamma=>c.
  case=>{c} // m a E.
  by apply/Fk/In_Work/E.
(* gamma = a :: gamma *)
case: a=>l a /=; rewrite ltnS.
elim: a l.
- (* a = Falsum *)
  rewrite /weight add1n => l L.
  by apply/(rule_shift_gamma_work _ _ NFalsum)/IH.
- (* a = Atom i *)
  rewrite /weight add1n=> i l L.
  by apply/(rule_shift_gamma_work _ _ (NAtom i))/IH.
- (* a = AndF a b *)
  move=>a _ b _ l; rewrite /weight -/weight addSn.
  case: l=>[|i1 l] L.
  - apply/rule_vimp_conj_gamma/(IH _ [:: ([::], a), ([::], b) & gamma])=>/=.
    by rewrite addnA.
  case: l=>[|i2 l].
  - apply/rule_vimp_conj_gamma/(IH _ [:: ([::i1], a), ([::i1], b) & gamma])=>/=.
    by rewrite addnA.
  apply: (rule_vimp_conj_gamma_new _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: ([::j], a), ([::j], b) & gamma])=>/=.
  by rewrite addnA.
- (* --------- a = OrF a b ---------- *)
  move=>+ _ b _ l; case.
  - (* a = Falsum *)
    rewrite /weight -/weight addSn => L.
    by apply/rule_vimp_falsum_or_a_gamma/(IH _ ((l, b) :: gamma)).
  - (* a = Atom i0 *)
    move=> i0; case b.
    - (* b = Falsum *)
      rewrite /weight -/weight add2n => L.
      apply/rule_vimp_a_or_falsum_gamma/(IH _ ((l, Atom i0) :: gamma)).
      by rewrite /= /weight -/weight add1n.
    - (* b = Atom i1 *)
      rewrite /weight -/weight add2n => i1 L.
      apply/(rule_shift_gamma_work _ _ (NDisj i0 i1))/IH.
      by apply/ltn_trans/L.
    - (* b = AndF b0 b1 *)
      move=>b0 b1; rewrite /weight -/weight !addSn=> L.
      apply: (rule_vimp_atom_or_a_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
      apply: (IH _ (([::j], AndF b0 b1) :: gamma)).
      by rewrite /= /weight -/weight addSn.
    - (* b = OrF b0 b1 *)
      move=>b0 b1; rewrite /weight -/weight addSn => L.
      apply: (rule_vimp_atom_or_a_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
      by apply: (IH _ (([::j], OrF b0 b1) :: gamma)).
    (* b = Imp b0 b1 *)
    move=> b0 b1; rewrite /weight /weight_neg -/weight -/weight_neg addSn => L.
    apply: (rule_vimp_atom_or_a_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    by apply: (IH _ (([::j], Imp b0 b1) :: gamma)).
  - (* a = AndF a0 a0 *)
    move=>a0 a1; rewrite /weight -/weight addnS !addSn addnA=>L.
    apply: (rule_vimp_a_or_b_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, OrF (Atom j) b), ([::j], AndF a0 a1) & gamma]).
    by rewrite /= /weight -/weight !addSn addnS !addnA.
  - (* a = OrF a0 a1 *)
    move=>a0 a1; rewrite /weight -/weight !addSn =>L.
    apply: (rule_vimp_a_or_b_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, OrF (Atom j) b), ([::j], OrF a0 a1) & gamma]).
    by rewrite /= /weight -/weight addSn addnA.
  (* a = Imp a0 a1 *)
  move=>a0 a1; rewrite /weight /weight_neg -/weight -/weight_neg !addSn addnA=>L.
  apply: (rule_vimp_a_or_b_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: (l, OrF (Atom j) b), ([::j], Imp a0 a1) & gamma]).
  by rewrite /= /weight /weight_neg -/weight -/weight_neg addSn !addnA.
(******************* a = Imp a c *****************************)
move=>+ _ c; case.
- (* a = Falsum  *)
  move=>_ l; rewrite /weight /weight_neg -/weight -/weight_neg add0n=>L.
  apply/rule_vimp_falsum_imp_b_gamma/IH.
  rewrite -add1n; apply/leq_trans/L; rewrite leq_add2r.
  by apply: weight_ge_1.
- (* a = Atom i0 *)
  move=>i0 IHc l; rewrite /weight /weight_neg -/weight -/weight_neg add0n=>L.
  by apply/rule_vimp_atom_imp_b_gamma/IHc.
- (* a = AndF a b *)
  move=> a b _ l; rewrite /weight /weight_neg -/weight -/weight_neg !addSn=>L.
  apply/rule_vimp_and_imp_gamma/(IH _ ((l, Imp a (Imp b c)) :: gamma)).
  by rewrite /= /weight /weight_neg -/weight -/weight_neg addnA.
- (* a = OrF a b *)
  move=>a b _ l; rewrite /weight /weight_neg -/weight -/weight_neg !addSn.
  case: c.
  - (* c = Falsum *)
    rewrite /weight -/weight addn1 addSn => L.
    apply/rule_vimp_or_imp_gamma/(IH _ [:: (l, Imp a Falsum), (l, Imp b Falsum) & gamma]).
    rewrite /= /weight /weight_neg -/weight -/weight_neg !addn1 !addSn addnS addnA.
    by apply/ltn_trans/L.
  - (* c = Atom i *)
    move=>i; rewrite /weight -/weight addn1 addSn => L.
    apply/rule_vimp_or_imp_gamma/(IH _ [::(l, Imp a (Atom i)), (l, Imp b (Atom i)) & gamma]).
    rewrite /= /weight /weight_neg -/weight -/weight_neg !addn1 !addSn addnS addnA.
    by apply/ltn_trans/L.
  - (* c = AndF c0 c1 *)
    move=>c0 c1; rewrite /weight -/weight addnS addSn addnA=>L.
    apply: (rule_vimp_or_imp_gamma_new _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, Imp a (Atom j)), (l, Imp b (Atom j)),
                     ([::j], AndF c0 c1) & gamma]).
    by rewrite /= /weight /weight_neg -/weight -/weight_neg !addn1 !addSn !addnS !addnA.
  - (* c = OrF c0 c1 *)
    move=>c0 c1; rewrite /weight -/weight => L.
    apply: (rule_vimp_or_imp_gamma_new _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, Imp a (Atom j)), (l, Imp b (Atom j)),
                     ([::j], OrF c0 c1) & gamma]).
    by rewrite /= /weight /weight_neg -/weight -/weight_neg !addn1 !addSn !addnS !addnA.
  (* c = Imp c0 c1 *)
  move=>c0 c1; rewrite /weight /weight_neg -/weight -/weight_neg addnA => L.
  apply: (rule_vimp_or_imp_gamma_new _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: (l, Imp a (Atom j)), (l, Imp b (Atom j)),
                   ([::j], Imp c0 c1) & gamma]).
  by rewrite /= /weight /weight_neg -/weight -/weight_neg !addn1 !addSn !addnS !addnA.
(* a = Imp a b *)
move=>+ b _ l; case.
- (* a = Falsum *)
  rewrite /weight /weight_neg -/weight -/weight_neg add1n addSn=>L.
  by apply/rule_vimp_falsum_imp_imp_gamma/(IH _ ((l, c) :: gamma)).
- (* a = Atom i0 *)
  move=>i0; case: b.
  - (* b = Falsum *)
    rewrite /weight /weight_neg -/weight -/weight_neg add2n !addSn=>L.
    apply: (rule_vimp_imp_falsum_imp_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ ((l, Imp (Imp (Atom i0) (Atom j)) c) :: gamma)).
    by rewrite /= /weight /weight_neg -/weight -/weight_neg add1n addSn.
  - (* b = Atom i1 *)
    move=>i1; case: c.
    - (* c = Falsum *)
      rewrite /weight /weight_neg -/weight -/weight_neg add1n add2n=>L.
      apply/(rule_shift_gamma_work _ _ (NImp_NF (NImp i0 i1 NFalsum)))/IH.
      by apply/ltn_trans/L.
    - (* c = Atom i2 *)
      move=>i2; rewrite /weight /weight_neg -/weight -/weight_neg add1n add2n=>L.
      apply/(rule_shift_gamma_work _ _ (NImp_NF (NImp i0 i1 (NAtom i2))))/IH.
      by apply/ltn_trans/L.
    - (* c = AndF c0 c1 *)
      move=>c0 c1; rewrite /weight /weight_neg -/weight -/weight_neg add1n !addSn=>L.
      apply: (rule_vimp_imp_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
      apply: (rule_shift_gamma_work _ _ (NImp_NF (NImp i0 i1 (NAtom j)))).
      by apply: (IH _ (([::j], AndF c0 c1) :: gamma)).
    - (* c = OrF c0 c1 *)
      move=>c0 c1; rewrite /weight /weight_neg -/weight -/weight_neg add1n addSn=>L.
      apply: (rule_vimp_imp_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
      apply: (rule_shift_gamma_work _ _ (NImp_NF (NImp i0 i1 (NAtom j)))).
      by apply: (IH _ (([::j], OrF c0 c1) :: gamma)).
    (* c = Imp c0 c1 *)
    move=>c0 c1; rewrite /weight /weight_neg -/weight -/weight_neg add1n addSn=>L.
    apply: (rule_vimp_imp_gamma _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (rule_shift_gamma_work _ _ (NImp_NF (NImp i0 i1 (NAtom j)))).
    by apply: (IH _ (([::j], Imp c0 c1) :: gamma)).
  - (* (Imp (Imp (Atom i0) (AndF b0 b1)) c) *)
    move=>b0 b1; rewrite /weight /weight_neg -/weight -/weight_neg !addSn=>L.
    apply: (rule_atom_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, Imp (Imp (Atom i0) (Atom j)) c),
                     (i0 :: l, Imp (AndF b0 b1) (Atom j)) & gamma]).
    by rewrite /= /weight /weight_neg -/weight -/weight_neg add1n addn1 !addSn !addnS addnC addnAC.
  - (* (Imp (Imp (Atom i0) (OrF b0 b1)) c) *)
    move=>b0 b1; rewrite /weight /weight_neg -/weight -/weight_neg !addSn=>L.
    apply: (rule_atom_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
    apply: (IH _ [:: (l, Imp (Imp (Atom i0) (Atom j)) c),
                     (i0 :: l, Imp (OrF b0 b1) (Atom j)) & gamma]).
    by rewrite /= /weight /weight_neg -/weight -/weight_neg add1n addn1 !addSn !addnS addnC addnAC.
  (* (Imp (Imp (Atom i0) (Imp b0 b1)) c) *)
  move=>b0 b1; rewrite /weight /weight_neg -/weight -/weight_neg !addSn=>L.
  apply: (rule_atom_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: (l, Imp (Imp (Atom i0) (Atom j)) c),
                   (i0 :: l, Imp (Imp b0 b1) (Atom j)) & gamma]).
  by rewrite /= /weight /weight_neg -/weight -/weight_neg add1n addn1 !addSn !addnS addnC addnAC.
- (* (Imp (Imp (AndF a0 a1) b) c) *)
  move=>a0 a1; rewrite /weight /weight_neg -/weight -/weight_neg
    addnS !addSn (addnAC _ _ (weight c)) addnA -!addSn => L.
  apply: (rule_a_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: (l, Imp (Imp (Atom j) b) c),
                   ([::j], AndF a0 a1) & gamma]).
  rewrite /= /weight /weight_neg -/weight -/weight_neg addSn addnS !addnA -!addSn.
  by apply/leq_trans/L; rewrite !leq_add2r !ltnS; case: {L}b.
- (* (Imp (Imp (OrF a0 a1) b) c) *)
  move=>a0 a1; rewrite /weight /weight_neg -/weight -/weight_neg -!addSn => L.
  apply: (rule_a_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  apply: (IH _ [:: (l, Imp (Imp (Atom j) b) c),
                   ([::j], OrF a0 a1) & gamma]).
  rewrite /= /weight /weight_neg -/weight -/weight_neg addnA (addnAC _ (weight c)) -!addSn.
  by apply/leq_trans/L; rewrite !leq_add2r; case: {L}b.
(* (Imp (Imp (Imp a0 a1) b) c) *)
move=>a0 a1; rewrite /weight /weight_neg -/weight -/weight_neg -!addSn => L.
apply: (rule_a_imp_b_imp_c_gamma _ _ _ _ _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
apply: (IH _ [:: (l, Imp (Imp (Atom j) b) c),
                 ([::j], Imp a0 a1) & gamma]).
rewrite /= /weight /weight_neg -/weight -/weight_neg addnA (addnAC _ (weight c)) -!addSn.
by apply/leq_trans/L; rewrite !leq_add2r; case: {L}b.
Qed.

(********************************************************************)

Lemma search_goal_invariant_weight n (goal : form nat) gamma work ctx j :
  (weight_goal goal < n)%N -> csearch_spec goal gamma work ctx j.
Proof.
elim: n =>[|n IH] // in goal gamma work ctx j *; rewrite ltnS.
case: goal=>/=.
- (* goal = Falsum *)
  move=>L.
  apply: (rule_gamma_falsum _ _ _ _ j.+1); first by rewrite ltEnat /=.
  rewrite (vlist_eq gamma).
  by apply: (search_atom_aux (weight_gamma (vlist2hlist (list2vlist gamma))).+1).
- (* goal = Atom i *)
  move=>i L.
  rewrite (vlist_eq gamma).
  by apply: (search_atom_aux (weight_gamma (vlist2hlist (list2vlist gamma))).+1).
- (* goal = AndF g0 g1 *)
  move=>g0 g1 L.
  apply: (rule_gamma_a _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  by apply: IH.
- (* goal = OrF g0 g1 *)
  move=>g0 g1 L.
  apply: (rule_gamma_a _ _ _ _ _ j.+1); first by rewrite ltEnat /=.
  by apply: IH.
(* goal = Imp g0 g1 *)
move=>g0 g1 L.
by apply/rule_gamma_a_imp_b/IH.
Qed.

Lemma search_goal_invariant (goal : form nat) gamma work ctx j :
  csearch_spec goal gamma work ctx j.
Proof. by apply: (search_goal_invariant_weight (weight_goal goal).+1). Qed.

(********************************************************************)

Theorem search (goal : form nat) gamma : search_spec goal gamma.
Proof.
move: (max_int_of_list_below (goal :: gamma)).
set j := max_int_of_list (goal :: gamma).
move=>/= /andP [Bj Bg].
case: (search_goal_invariant goal gamma [::] gamma j)=>//.
- rewrite /sound=>/= a; case=>{a} //= n a E.
  by apply/(Derivable_Intro _ _ (Var n))/ByAssumption.
- rewrite /minimal=> k M Fk a /onth_index E.
  by apply/Fk/(In_Gamma _ _ (index a gamma)).
- apply: Sderivable.
move=>k Mk Fk Nk.
apply: (Srefutable _ _ k)=>// a /onth_index E.
by apply/Fk/(In_Gamma _ _ (index a gamma)).
Qed.

End SearchNat.
