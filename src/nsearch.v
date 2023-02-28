From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap forms normal_forms kripke_trees in_ngamma
                           catrev disjunct
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
  set aot := (update_atoms i a).
  case La: aot=>[a' ot]; move: La.
  rewrite (surjective_pairing aot); case=>_.
  rewrite lookup_upsert //; case: ot=>[[]|] La.
  - apply: contradiction_atoms=>//; first by apply/optP; exists tt.
    by apply: IHw.
  case Lai: (delete i ai)=>[ai' obs]; move: Lai.
  rewrite (surjective_pairing (delete _ _)); case=>_.
  rewrite lookup_delete //; case: obs=>[bs|] Lai.
  - apply: (left_p_imp_ai _ _ _ _ _ bs)=>//.
    apply: IHn.
    - by apply: invariant_upsert.
    - by apply: invariant_delete.
    - apply: (leq_trans (n:=nweight_Sequent work ds ni ai)).
      - by apply: nweight_shift_ai_work.
      by apply/leq_trans/L.
    - by apply: regular_del.
    - by apply: disjs_delete_ai.
    by apply: goal_disj_insert_a.
  apply: rule_shift_work_a=>//.
  apply: IHw=>//.
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

(*
Theorem nsearch :
 forall (goal : Int) (work : nf_list) (ctx : flist),
 (forall (n : nat) (a : normal_form),
  my_nth normal_form n work a -> Derivable ctx (nf2form a)) ->
 (forall (a : form) (k : kripke_tree),
  Is_Monotone_kripke_tree k ->
  (forall b : normal_form, In b work -> forces_t k (nf2form b)) ->
  In a ctx -> forces_t k a) ->
 nsearch_spec_result_aux goal work DNil NNil AI_Nil ANil ctx.
intros goal work ctx sound minimal.
elim
 (nsearch_aux (S (nweight_Sequent work DNil NNil AI_Nil)) goal work DNil NNil
    AI_Nil ANil ctx).
intros ni1 le1.
cut (ni1 = NNil).
intros claim.
 rewrite claim.
intros; assumption.
inversion_clear le1.
trivial.
apply Nat.lt_succ_diag_r.

unfold AI_Nil in |- *.
unfold nf_list in |- *.
apply regular_AVL_NIL.

unfold a_ai_disj in |- *.
intros i lookup_i bs lookup_bs.
inversion_clear lookup_i.

unfold a_goal_disj in |- *.
intros lookup_goal.
inversion_clear lookup_goal.

unfold deco_sound in |- *.
intros k i0 i1 b in_k.
inversion_clear in_k.

unfold nsound in |- *.
intros a in_ngamma.
elim in_ngamma; clear in_ngamma a.

intros n a nth.
apply sound with n; assumption.

intros n i j nth; elimtype False; inversion_clear nth.
intros n x nth; elimtype False; inversion_clear nth.
intros i b n bs lookup_i nth; elimtype False; inversion_clear lookup_i.
intros i lookup; elimtype False; inversion_clear lookup.

unfold nminimal in |- *.
intros a k k_is_mon k_forces_gamma in_a.
apply minimal; try assumption.
intros b in_b.
elim (in_nth normal_form b work in_b).
intros n nth.
apply k_forces_gamma.
apply In_Work with n; assumption.
Qed.
*)

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

Extraction "ext.ml" nsearch_aux.
