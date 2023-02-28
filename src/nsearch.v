From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap forms normal_forms kripke_trees in_ngamma
                           catrev disjunct forces_ngamma derivable_def ndeco_sound nsound nminimal
                           le_ks lt_ks nweight nrules.

Section NSearch.
Context {disp : unit} {A : orderType disp}.

Definition nsearch_invariant (n : nat) :=
  forall (goal : A) (work : seq (normal_form A)) (ds : seq (disj A))
         (ni : seq (nested_imp A)) (ai : atomic_imps A) (a : atoms A)
         (ctx : seq (form A)),
  invariant a ->
  invariant ai ->
  (nweight_Sequent work ds ni ai < n)%N ->
  regular ai ->
  a_ai_disj a ai ->
  a_goal_disj a goal ->
  nsearch_spec goal work ds ni ai a ctx.

Lemma nsearch_aux n : nsearch_invariant n.
Proof.
rewrite /nsearch_invariant; elim: n=>// n IHn goal work ds ni ai a ctx.
(* 0 < n *)
rewrite ltnS; elim: work ds ni ai a.
- (* work = [::] *)
  case=>[|[i j] ds] ni ai a Ha Hai L R D G.
  - (* ds = [::] *)
    move: L; apply: (@lt_ks_rec _ _ (fun ni => (_ <= _)%N -> _) _ ni).
    case=>/=; first by move=>*; apply: fail.
    case=>[[a0 a1 n2]|x2 k2] ni2 dni IHl L.
    - apply: left_nimp.
      - move=>ni1 L1; case H: (lookup a a1)=>[[]|].
        - by apply/nax/In_Atoms/optP; exists tt.
        apply/IHn=>//; last by apply/negOptP.
        rewrite -(@nweight_sequent_nimp_left _ _ _ _ _ _ _ ni2 _ dni) //.
        by apply: le_eqv.
      - move=>ni1 L1.
        apply: IHn=>//.
        rewrite (@nweight_sequent_nimp_right _ _ _ _ _ _ _ _ ni1) in L.
        - by apply/ltn_trans/L.
        by apply: ge_eqv.
      move=>/= ni1 k L1.
      apply: (IHl ni1 [::])=>/=.
      - by apply: (lt_ks_shift_nd _ _ _ _ _ k).
      rewrite (nweight_sequent_eqv _ _ _ (catrev_d dni (Undecorated (NImp a0 a1 n2) :: ni2))) //.
      apply: eqv_ni_trans; first by apply/le_eqv/L1.
      apply: le_eqv; rewrite !rev_app_app.
      by apply: le_ni_app_dn=>//; apply: le_ni_refl.
    apply: shift_ni_dni; apply: IHl=>//.
    by apply: lt_ks_shift_dd.
  (* ds=(i,j)::ds) *)
  apply: left_disj=>ni0 L0; apply: IHn=>//.
  - rewrite -(@nweight_sequent_left_disj_left _ _ _ j _ _ ni) //.
    by apply: le_eqv.
  rewrite -(@nweight_sequent_left_disj_right _ _ i _ _ _ ni) //.
  by rewrite eqv_ni_sym.
(* work = _ :: _ *)
move=>+ work IHw ds ni ai a Ha Hai + R D G; case.
- (* a = NFalsum *)
  by move=>L; apply: nefq.
- (* a = NAtom i *)
  move=>i L.
  case: (eqVneq goal i)=>[<-|N].
  - by apply/nax/in_ngamma_cons_work_head.
  case La: (update_atoms i a)=>[a' ot]; move: La.
  rewrite (surjective_pairing (update_atoms _ _)); case=>Ha'.
  rewrite lookup_upsert //; case: ot=>[[]|] La.
  - apply: contradiction_atoms=>//; first by apply/optP; exists tt.
    by apply: IHw.
  case Lai: (delete i ai)=>[ai' obs]; move: Lai.
  rewrite (surjective_pairing (delete _ _)); case=>Hai'.
  rewrite lookup_delete //; case: obs=>[bs|] Lai.
  - apply: (left_p_imp_ai _ _ _ _ _ bs _ ai' _ a')=>//.
    apply: IHn; rewrite -?Hai' -?Ha'.
    - by apply: invariant_upsert.
    - by apply: invariant_delete.
    - apply: (leq_trans (n:=nweight_Sequent work ds ni ai)).
      - by apply: nweight_shift_ai_work.
      by apply/leq_trans/L.
    - by apply: regular_del.
    - by apply: disjs_delete_ai.
    by apply: goal_disj_insert_a.
  apply: (rule_shift_work_a goal _ _ _ _ _ _ a')=>//.
  apply: IHw=>//; rewrite -Ha'.
  - by apply: invariant_upsert.
  - by apply: disjs_insert_a=>//; apply/negOptP.
  by apply: goal_disj_insert_a.
- (* a = OrF (Atom i) (Atom j) *)
  move=>i j L.
  apply/rule_shift_work_ds/IHw=>//.
  by rewrite -nweight_shift_work_ds.
- (* a = AImp i b *)
  move=>i b L.
  case La : (lookup a i)=>[[]|].
  - apply: left_p_imp_work; first by apply/optP; exists tt.
    by apply: IHn.
  apply: rule_shift_work_ai=>//.
  apply: IHw=>//.
  - by apply: invariant_upsert.
  - by rewrite -nweight_shift_work_ai.
  - by apply: regular_ins.
  by apply: disjs_insert_ai=>//; apply/negOptP.
(* a = NImp x *)
move=>x L.
apply/rule_shift_work_ni0/IHw=>//.
by rewrite -nweight_shift_work_ni0.
Qed.

Theorem nsearch (goal : A) work ctx :
  (forall n a, onth work n = Some a -> Derivable ctx (nf2form a)) ->
  (forall k, Is_Monotone_kripke_tree k ->
    {in work, forall b, forces_t k (nf2form b)} ->
    {in ctx, forall a, forces_t k a}) ->
  nsearch_spec_result_aux goal work [::] [::] leaf leaf ctx.
Proof.
move=>S M.
case: (nsearch_aux (nweight_Sequent work [::] [::] leaf).+1 goal work [::] [::] leaf leaf ctx)=>//.
- by rewrite /nsound=>a; case.
- rewrite /nminimal=>k Mk Fk.
  apply: M=>// b /onth_index Hb.
  by apply/Fk/In_Work/Hb.
move=>ni1 Ln.
suff ->: ni1 = [::] by [].
by case: ni1 Ln=>//=; case.
Qed.

End NSearch.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Set Extraction Flag 522.
Extract Inlined Constant negb => "not".
Extract Inlined Constant idP => "".
Extract Inlined Constant eqn => "equal".  (* ints! *)
Extract Inlined Constant size => "length".
Extract Inductive reflect => bool [ true false ].
Extract Inductive alt_spec => bool [ true false ].
Extract Inductive eq_xor_neq => bool [ true false ].
Extract Inductive leq_xor_gtn => bool [ true false ].
Extract Inductive ltn_xor_geq => bool [ true false ].

Extraction "ext.ml" nsearch.
