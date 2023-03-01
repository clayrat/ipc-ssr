From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude forms normal_forms derivations trees kripke_trees
                           in_gamma forces_gamma derivable_def derivable_tools
                           sound minimal.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Section Rules.
Context {disp : unit} {A : orderType disp}.

Variant search_spec_aux (goal : form A) (gamma : seq (form A))
                        (work : seq (normal_form A)) (ctx : seq (form A)) : Type :=
  | derivable of Derivable ctx goal
  | refutable k of
      Is_Monotone_kripke_tree k &
      forces_gamma gamma work k &
      ~forces_t k goal.

Definition search_spec (goal : form A) (gamma : seq (form A))
                       (work : seq (normal_form A)) (ctx : seq (form A)) (i : A) : Type :=
  below_form goal i ->
  below_list gamma i ->
  below_list ctx i ->
  sound gamma work ctx ->
  minimal gamma work ctx ->
  search_spec_aux goal gamma work ctx.

(**********************************************************************)

Lemma rule_shift_gamma_work goal l a gamma work ctx j :
  search_spec goal gamma (nvimp l a :: work) ctx j ->
  search_spec goal (vimp l (nf2form a) :: gamma) work ctx j.
Proof.
rewrite (vimp_eq_nvimp l a) /search_spec=>/= + Hg0 /andP [Hb Hg] Hc S M.
case=>//.
- by apply: sound_shift_gamma_work.
- by apply: minimal_shift_gamma_work.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
by apply: forces_gamma_shift_work_gamma.
Qed.

(*********************************************************************)

Lemma search_spec_subst_gamma_pos goal gamma work ctx j j1 a b c :
  j < j1 ->
  (below_form c j -> [/\ below_form a j, below_form b j1 & subst_form j a b = c]) ->
  (forall k, Is_Monotone_kripke_tree k ->
   forces_t k b -> forces_t k (Imp (Atom j) a) -> forces_t k c) ->
  search_spec goal (b :: Imp (Atom j) a :: gamma) work
    (b :: Imp (Atom j) a :: ctx) j1 ->
  search_spec goal (c :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= L1 Bx F0 S0 Hg0 /andP [Hj Hg] Hc S M.
case: (Bx Hj)=>{Bx}Ba Bb Ec.
case: S0.
- by move: Hg0; apply/implyP/less_below_form_imply.
- rewrite -andbA; apply/and4P; split=>//.
  - by move: Ba; apply/implyP/less_below_form_imply.
  by move: Hg; apply/implyP/less_below_list_imply.
- rewrite -andbA; apply/and4P; split=>//.
  - by move: Ba; apply/implyP/less_below_form_imply.
  by move: Hc; apply/implyP/less_below_list_imply.
- do 2!apply: sound_cons_gamma_cons_ctx.
  by apply/sound_cons_gamma_tail/S.
- move: M; rewrite /minimal=>M k Mk Fk f.
  rewrite !inE; case/or3P=>[/eqP{f}->|/eqP{f}->|Hf].
  - by apply/Fk/in_gamma_cons_gamma_head.
  - by apply/Fk/in_gamma_cons_gamma_tail/in_gamma_cons_gamma_head.
  apply: M=>//.
  apply: (forces_gamma_cons_gamma_weak2 _ _ _ b (Imp (Atom j) a))=>//.
  by apply: F0.
- move=>D; apply: derivable.
  apply: (derivable_cut _ (subst_form j a (Imp (Atom j) a)))=>/=; rewrite eqxx.
  - by rewrite subst_form_below //; apply: derivable_a_imp_a.
  apply: (derivable_cut_merge _ c).
  - by apply/derivable_weak/S/in_gamma_cons_gamma_head.
  rewrite -Ec -(subst_form_below j a goal) // -(subst_list_below j a ctx) //.
  rewrite (_ : [:: subst_form j a b, Imp a (subst_form j a a) & subst_list j a ctx] =
               subst_list j a [:: b, Imp (Atom j) a & ctx]); last by rewrite /= eqxx.
  by apply: derivable_subst.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply: (forces_gamma_cons_gamma_weak2 _ _ _ b (Imp (Atom j) a))=>//.
by apply: F0.
Qed.

Lemma rule_vimp_a_gamma goal l a gamma work ctx j j1 :
  j < j1 ->
  search_spec goal (vimp [::j] a :: gamma) (nvimp l (NAtom j) :: work)
                   [:: vimp l (Atom j), Imp (Atom j) a & ctx] j1 ->
  search_spec goal (vimp l a :: gamma) work ctx j.
Proof.
move=>/= L1 S0.
apply: (search_spec_subst_gamma_pos _ _ _ _ _ j1 a (vimp l (Atom j)))=>//.
- move=>Bj.
  have H1 := below_vimp_tail _ _ _  Bj.
  move/implyP: (below_vimp_head j l a)=>/(_ Bj) {}Bj.
  split=>//.
  - move: (below_vimp_split j1 l (Atom j))=>/=; rewrite L1 /=; apply.
    by move=>i Hi; apply/lt_trans/L1/H1.
  by rewrite (subst_vimp_head j l a (Atom j)) //= eqxx.
- move=>k Mk F1 F2.
  apply: (forces_vimp_t _ _ (Atom j))=>//= k' S1 Fj.
  by apply: (F2 k').
by apply: (rule_shift_gamma_work _ _ (NAtom j)).
Qed.

Lemma rule_vimp_imp_gamma goal l a b gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [:: vimp l (Imp a (Atom j)), vimp [::j] b & gamma] work
                   [:: vimp l (Imp a (Atom j)), Imp (Atom j) b & ctx] j1 ->
  search_spec goal (vimp l (Imp a b) :: gamma) work ctx j.
Proof.
move=>/= L1 S0.
apply: (search_spec_subst_gamma_pos _ _ _ _ _ j1 b (vimp l (Imp a (Atom j))))=>//.
- move=>Bj.
  have H1 := below_vimp_tail _ _ _  Bj.
  move/implyP: (below_vimp_head j l (Imp a b))=>/(_ Bj) {Bj}/= /andP [Ba Bb].
  split=>//.
  - move: (below_vimp_split j1 l (Imp a (Atom j)))=>/=; rewrite L1 /= andbT.
    move: (less_below_form_imply a _ _ L1); rewrite Ba=>/= -> /=; apply.
    by move=>i Hi; apply/lt_trans/L1/H1.
  rewrite (subst_vimp_head j l b (Imp a (Atom j))) //= eqxx.
  by rewrite (subst_form_below j b a).
move=>k Mk F1 F2.
apply: (forces_vimp_t _ _ (Imp a (Atom j)))=>//= k' S1 Fj k'' S2 S3 Fa.
by apply: (F2 k'')=>//; apply: (Fj k'').
Qed.

(****************************************************)
(*                                                  *)
(* rules for   goal = ...                           *)
(*                                                  *)
(****************************************************)

Lemma rule_gamma_falsum gamma work ctx i j :
  i < j ->
  search_spec (Atom i) gamma work ctx j ->
  search_spec Falsum gamma work ctx i.
Proof.
rewrite /search_spec=>L S0 Bi Bg Bc S M.
case: S0=>//.
- by move: Bg; apply/implyP/less_below_list_imply.
- by move: Bc; apply/implyP/less_below_list_imply.
- by move=>D; apply/derivable/(snd_order_inst _ i).
move=>k Mk Fk Nk.
by apply: (refutable _ _ _ _ k).
Qed.

Lemma rule_gamma_a_imp_b a b gamma work ctx j :
  search_spec b (a :: gamma) work (a :: ctx) j ->
  search_spec (Imp a b) gamma work ctx j.
Proof.
rewrite /search_spec=>/= + /andP [Ba Bb] Bg Bc S M.
case=>//.
- by rewrite Ba.
- by rewrite Ba.
- by apply: sound_cons_gamma_cons_ctx.
- by apply: minimal_cons_gamma_cons_ctx.
- case=>[t Dt]; apply: derivable.
  by apply/(Derivable_Intro _ _ (Abs a t))/ImpIntro.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
- by apply/forces_gamma_cons_gamma_tail/Fk.
move: Nk=>/[swap] Fab; apply.
apply/forces_imp_app_t/Fab.
by apply/forces_gamma_cons_gamma_head/Fk.
Qed.

Lemma rule_gamma_a a gamma work ctx j j1 :
  j < j1 ->
  search_spec (Atom j) (Imp a (Atom j) :: gamma) work (Imp a (Atom j) :: ctx) j1 ->
  search_spec a gamma work ctx j.
Proof.
rewrite /search_spec=>/= L + Bj Bg Bc S M.
have Bj1 : below_form a j1 by move: Bj; apply/implyP/less_below_form_imply.
rewrite L Bj1 andbT /=.
case=>//.
- by move: Bg; apply/implyP/less_below_list_imply.
- by move: Bc; apply/implyP/less_below_list_imply.
- by apply: sound_cons_gamma_cons_ctx.
- by apply: minimal_cons_gamma_cons_ctx.
- move=>D; apply/derivable/(derivable_cut _ (Imp a a)).
  - by exact: derivable_a_imp_a.
  by move/(derivable_subst j a): D=>/=; rewrite eqxx subst_form_below // subst_list_below.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
- by apply/forces_gamma_cons_gamma_tail/Fk.
move: Nk=>/[swap] Fab; apply.
apply: (forces_imp_app_t _ a)=>//.
by apply/forces_gamma_cons_gamma_head/Fk.
Qed.

(***********************************************************************)
(***********************************************************************)

(**************************************************)
(* rules for   ... vimp l (AndF a b) :: gamma ... *)

Lemma rule_vimp_conj_gamma goal l b0 b1 gamma work ctx j :
  search_spec goal [:: vimp l b0, vimp l b1 & gamma] work ctx j ->
  search_spec goal (vimp l (AndF b0 b1) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- apply/and3P; split=>//; move: Bv; apply/implyP/below_vimp=>/= z; rewrite implybE negb_and.
  - by rewrite orbC orbA orbN.
  by rewrite -orbA orNb orbT.
- apply/sound_cons_gamma_weak2/S.
  move=>D; split; apply/derivable_vimp/D=>ctx'.
  - by apply: derivable_a_and_b__derivable_a.
  by apply: derivable_a_and_b__derivable_b.
- apply/minimal_cons_gamma_weak2/M=>k Mk F0 F1.
  by apply: (forces_vimp2_t _ _ b0 b1).
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak2/Fk=>F0 F1.
by apply: (forces_vimp2_t _ _ b0 b1).
Qed.

Lemma rule_vimp_conj_gamma_new goal l b0 b1 gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [::vimp [::j] b0, vimp [::j] b1 & gamma] (nvimp l (NAtom j) :: work)
                   [::vimp l (Atom j), Imp (Atom j) (AndF b0 b1) & ctx] j1 ->
  search_spec goal (vimp l (AndF b0 b1) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (rule_vimp_a_gamma _ _ _ _ _ _ _ j1)=>//.
by apply: rule_vimp_conj_gamma.
Qed.

(*************************************************)
(* rules for   ... vimp l (OrF a b) :: gamma ... *)

Lemma rule_vimp_falsum_or_a_gamma goal l a gamma work ctx j :
  search_spec goal (vimp l a :: gamma) work ctx j ->
  search_spec goal (vimp l (OrF Falsum a) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- by rewrite Bg0 andbT; move: Bv; apply/implyP/below_vimp.
- apply/sound_cons_gamma_weak/S/derivable_vimp=>ctx0.
  by apply: derivable_falsum_or_a__derivable_a.
- apply/minimal_cons_gamma_weak/M=>k Mk.
  by apply: forces_vimp_t=>* /=; right.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak/Fk.
by apply: forces_vimp_t=>* /=; right.
Qed.

Lemma rule_vimp_a_or_falsum_gamma goal l a gamma work ctx j :
  search_spec goal (vimp l a :: gamma) work ctx j ->
  search_spec goal (vimp l (OrF a Falsum) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- by rewrite Bg0 andbT; move: Bv; apply/implyP/below_vimp=>/= z; rewrite andbT.
- apply/sound_cons_gamma_weak/S/derivable_vimp=>ctx0.
  by apply: derivable_a_or_falsum__derivable_a.
- apply/minimal_cons_gamma_weak/M=>k Mk.
  by apply: forces_vimp_t=>* /=; left.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak/Fk.
by apply: forces_vimp_t=>* /=; left.
Qed.

Lemma rule_vimp_atom_or_a_gamma goal l i a gamma work ctx j j1 :
  j < j1 ->
  search_spec goal (Imp (Atom j) a :: gamma) (nvimp l (NDisj i j) :: work)
              [:: vimp l (OrF (Atom i) (Atom j)), Imp (Atom j) a & ctx] j1 ->
  search_spec goal (vimp l (OrF (Atom i) a) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (search_spec_subst_gamma_pos _ _ _ _ _ j1 a (vimp l (OrF (Atom i) (Atom j))))=>//.
- move=>Bj.
  have H1 := below_vimp_tail _ _ _  Bj.
  move/implyP: (below_vimp_head j l (OrF (Atom i) a))=>/(_ Bj) /= /andP [Hij {}Bj].
  split=>//.
  - move: (below_vimp_split j1 l (OrF (Atom i) (Atom j)))=>/=; rewrite L (lt_trans Hij L) /=; apply.
    by move=>k Hk; apply/lt_trans/L/H1.
  rewrite (subst_vimp_head j l a (OrF (Atom i) (Atom j))) //= eqxx.
  by move: Hij; rewrite lt_neqAle eq_sym; case/andP=>/negbTE->.
- move=>k Mk F1 F2.
  apply: (forces_vimp_t _ _ (OrF (Atom i) (Atom j)))=>//= k' S1.
  by case=>Fk; [left | right; apply: (F2 k')].
by apply: (rule_shift_gamma_work _ _ (NDisj i j)).
Qed.

Lemma rule_vimp_a_or_b_gamma goal l a b gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [:: vimp l (OrF (Atom j) b), vimp [::j] a & gamma]
              work [:: vimp l (OrF (Atom j) b), Imp (Atom j) a & ctx] j1 ->
  search_spec goal (vimp l (OrF a b) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (search_spec_subst_gamma_pos _ _ _ _ _ j1 a (vimp l (OrF (Atom j) b)))=>//.
- move=>Bj.
  have H1 := below_vimp_tail _ _ _  Bj.
  move/implyP: (below_vimp_head j l (OrF a b))=>/(_ Bj) /= /andP {Bj}[Ba Bb].
  have H2 : below_form b j1 by move: Bb; apply/implyP/less_below_form_imply.
  split=>//.
  - move: (below_vimp_split j1 l (OrF (Atom j) b))=>/=; rewrite L H2 /=; apply.
    by move=>k Hk; apply/lt_trans/L/H1.
  by rewrite (subst_vimp_head j l a (OrF (Atom j) b)) //= eqxx subst_form_below.
move=>k Mk F1 F2.
apply: (forces_vimp_t _ _ (OrF (Atom j) b))=>//= k' S1.
by case=>Fk; [left; apply: (F2 k') | right].
Qed.

(******************************************************)
(* rules for   ... vimp l (Imp Falsum b) :: gamma ... *)

Lemma rule_vimp_falsum_imp_b_gamma goal l b gamma work ctx j :
  search_spec goal gamma work ctx j ->
  search_spec goal (vimp l (Imp Falsum b) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- by apply/sound_cons_gamma_tail/S.
- rewrite /minimal=>k Mk Fk.
  apply: M=>//.
  apply/forces_gamma_cons_gamma/Fk.
  by apply: forces_vimp0_t=>*.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma/Fk.
by apply: forces_vimp0_t=>*.
Qed.

(*********************************************************)
(* rules for   ... vimp l (Imp (Atom i) b)) :: gamma ... *)

Lemma rule_vimp_atom_imp_b_gamma goal l i b gamma work ctx j :
  search_spec goal (vimp (i :: l) b :: gamma) work ctx j ->
  search_spec goal (vimp l (Imp (Atom i) b) :: gamma) work ctx j.
Proof. by []. Qed.


(***************************************************)
(* rules for   ... Imp (AndF a0 a1) b :: gamma ... *)

Lemma rule_vimp_and_imp_gamma goal l a0 a1 b gamma work ctx j :
  search_spec goal (vimp l (Imp a0 (Imp a1 b)) :: gamma) work ctx j ->
  search_spec goal (vimp l (Imp (AndF a0 a1) b) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- rewrite Bg0 andbT.
  by move: Bv; apply/implyP/below_vimp=>z /=; rewrite andbA.
- apply/sound_cons_gamma_weak/S/derivable_vimp=>ctx'.
  by apply: derivable_a_and_b_imp_c__derivable_a_imp_b_imp_c.
- apply/minimal_cons_gamma_weak/M=>k Mk Fk.
  apply/forces_vimp_t/Fk=>k' S1 F'.
  rewrite /forces_t2; apply: forces_uncurry=>//.
  by case/kripke_tree_kripke_model: Mk.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak/Fk/forces_vimp_t=>k' S1 F'.
rewrite /forces_t2; apply: forces_uncurry=>//.
by case/kripke_tree_kripke_model: Mk.
Qed.

(***********************************************************)
(* rules for   ... vimp l (Imp (OrF a0 a1) b) :: gamma ... *)

Lemma rule_vimp_or_imp_gamma goal l a0 a1 b gamma work ctx j :
  search_spec goal [:: vimp l (Imp a0 b), vimp l (Imp a1 b) & gamma] work ctx j ->
  search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- by rewrite Bg0 andbT; apply/andP; split; move: Bv; apply/implyP/below_vimp=>z /=;
     apply/implyP; [rewrite andbAC | rewrite -andbA]; case/andP.
- apply/sound_cons_gamma_weak2/S=>D; split; apply/derivable_vimp/D=>ctx'.
  - by apply: derivable_a_or_b_imp_c__derivable_a_imp_c.
  by apply: derivable_a_or_b_imp_c__derivable_b_imp_c.
- apply/minimal_cons_gamma_weak2/M=>k Mk F0 F1.
  apply/(forces_vimp2_t _ _ (Imp a0 b) (Imp a1 b))=>// k' S1 F0' F1'.
  by rewrite /forces_t2; apply: forces_imp_or.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak2/Fk/forces_vimp2_t=>k' S1 F'.
by rewrite /forces_t2; apply: forces_imp_or.
Qed.

Lemma rule_vimp_or_imp_gamma_new goal l a0 a1 b gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [:: vimp l (Imp a0 (Atom j)), vimp l (Imp a1 (Atom j)), vimp [::j] b & gamma] work
                   [:: vimp l (Imp (OrF a0 a1) (Atom j)), Imp (Atom j) b & ctx] j1 ->
  search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (rule_vimp_imp_gamma _ _ _ _ _ _ _ _ j1)=>//.
by apply: rule_vimp_or_imp_gamma.
Qed.

(*********************************************************)
(* rules for   ... vimp l (Imp (Imp a b) c) :: gamma ... *)

Lemma rule_vimp_falsum_imp_imp_gamma goal l b c gamma work ctx j :
  search_spec goal (vimp l c :: gamma) work ctx j ->
  search_spec goal (vimp l (Imp (Imp Falsum b) c) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= + Bg /andP [Bv Bg0] Bc S M.
case=>//.
- rewrite Bg0 andbT; move: Bv; apply/implyP/below_vimp=>z /=.
  by rewrite implybE negb_and -orbA orNb orbT.
- apply/sound_cons_gamma_weak/S/derivable_vimp=>ctx'.
  by apply: derivable_falsum_imp_b_imp_c__derivable_c.
- apply/minimal_cons_gamma_weak/M=>k Mk.
  apply/forces_vimp_t=> k' S1 F'.
  case/kripke_tree_kripke_model: Mk=>_ Wt Wm.
  by rewrite /forces_t2; apply: forces_imp.
- by apply: derivable.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak/Fk/forces_vimp_t=>k' S1 F'.
case/kripke_tree_kripke_model: Mk=>_ Wt Wm.
by rewrite /forces_t2; apply: forces_imp.
Qed.

Lemma rule_vimp_imp_falsum_imp_gamma goal l a c gamma work ctx j j1 :
  j < j1 ->
  search_spec goal (vimp l (Imp (Imp a (Atom j)) c) :: gamma) work
                   (vimp l (Imp (Imp a (Atom j)) c) :: ctx) j1 ->
  search_spec goal (vimp l (Imp (Imp a Falsum) c) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= L S0 Bg /andP [Bv Bg0] Bj S M.
have H1 := below_vimp_tail _ _ _  Bv.
move/implyP: (below_vimp_head j l (Imp (Imp a Falsum) c))=>/(_ Bv) /=.
rewrite andbT => {Bv}/andP [Ba Bc].
have Bf: below_form (vimp l (Imp (Imp a (Atom j)) c)) j1.
- have: below_form (Imp (Imp a (Atom j)) c) j1.
  - rewrite /= L andbT; apply/andP; split.
    - by move: Ba; apply/implyP/less_below_form_imply.
    by move: Bc; apply/implyP/less_below_form_imply.
  by apply/implyP/below_vimp_split=>z Hz; apply/lt_trans/L/H1.
case: S0.
- by move: Bg; apply/implyP/less_below_form_imply.
- apply/andP; split=>//.
  by move: Bg0; apply/implyP/less_below_list_imply.
- apply/andP; split=>//.
  by move: Bj; apply/implyP/less_below_list_imply.
- by apply/sound_cons_gamma_cons_ctx/sound_cons_gamma_tail/S.
- rewrite /minimal=>k Mk Fk x.
  rewrite inE; case/orP=>[/eqP{x}->|Hx].
  - by apply/Fk/in_gamma_cons_gamma_head.
  apply: M=>//.
  apply/forces_gamma_cons_gamma_weak/Fk/forces_vimp_t=>k' S1 F2.
  by apply: (forces_imp_imp_false_r _ _ _ _ _ (Atom j)).
- move=>D; apply/derivable/(derivable_cut_merge _ (vimp l (Imp (Imp a Falsum) c))).
  - by apply/S/in_gamma_cons_gamma_head.
  rewrite (_ : goal = subst_form j Falsum goal); last by apply/esym/subst_form_below.
  rewrite (_ : vimp l (Imp (Imp a Falsum) c) :: ctx =
               subst_list j Falsum (vimp l (Imp (Imp a (Atom j)) c) :: ctx)); last first.
  - by rewrite /= subst_vimp_head //= subst_form_below // eqxx subst_list_below // subst_form_below.
  by apply: derivable_subst.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply/forces_gamma_cons_gamma_weak/Fk/forces_vimp_t=>k' S1 F2.
by apply: (forces_imp_imp_false_r _ _ _ _ _ (Atom j)).
Qed.

Lemma rule_atom_imp_atom_imp_c_gamma goal l a b c gamma work ctx j j1 :
  j < j1 ->
  search_spec goal (Imp (Atom j) c :: gamma) (nvimp l (NImp_NF (NImp a b (NAtom j))) :: work)
                   [:: vimp l (Imp (Imp (Atom a) (Atom b)) (Atom j)), Imp (Atom j) c & ctx] j1 ->
  search_spec goal (vimp l (Imp (Imp (Atom a) (Atom b)) c) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (rule_vimp_imp_gamma _ _ _ _ _ _ _ _ j1)=>//.
by apply: (rule_shift_gamma_work _ _ (NImp_NF (NImp a b (NAtom j)))).
Qed.

Lemma rule_atom_imp_b_imp_c_gamma goal l a b c gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [:: vimp l (Imp (Imp (Atom a) (Atom j)) c), vimp (a :: l) (Imp b (Atom j)) & gamma] work
                   [:: vimp l (Imp (Imp (Atom a) (Atom j)) c), vimp (a :: l) (Imp b (Atom j)) & ctx] j1 ->
  search_spec goal (vimp l (Imp (Imp (Atom a) b) c) :: gamma) work ctx j.
Proof.
rewrite /search_spec=>/= L S0 Bg /andP [Bv Bg0] Bj S M.
have H1 := below_vimp_tail _ _ _  Bv.
move/implyP: (below_vimp_head j l (Imp (Imp (Atom a) b) c))=>/(_ Bv) /=.
rewrite -andbA; case/and3P=>Ha Bb Bc.
have B10 : below_form (vimp l (Imp (Imp (Atom a) (Atom j)) c)) j1.
- have: below_form (Imp (Imp (Atom a) (Atom j)) c) j1.
  - rewrite /= L andbT; apply/andP; split.
    - by apply/lt_trans/L.
    by move: Bc; apply/implyP/less_below_form_imply.
  by apply/implyP/below_vimp_split=>z Hz; apply/lt_trans/L/H1.
have B11: below_form (vimp l (Imp (Atom a) (Imp b (Atom j)))) j1.
- have: below_form (Imp (Atom a) (Imp b (Atom j))) j1.
  - rewrite /= L andbT; apply/andP; split.
    - by apply/lt_trans/L.
    by move: Bb; apply/implyP/less_below_form_imply.
  by apply/implyP/below_vimp_split=>z Hz; apply/lt_trans/L/H1.
case: S0.
- by move: Bg; apply/implyP/less_below_form_imply.
- apply/and3P; split=>//.
  by move: Bg0; apply/implyP/less_below_list_imply.
- apply/and3P; split=>//.
  by move: Bj; apply/implyP/less_below_list_imply.
- do 2!apply: sound_cons_gamma_cons_ctx.
  by apply/sound_cons_gamma_tail/S.
- rewrite /minimal => k Mk Fk x.
  rewrite !inE; case/or3P=>[/eqP{x}->|/eqP{x}->|Hx].
  - by apply/Fk/in_gamma_cons_gamma_head.
  - by apply/Fk/in_gamma_cons_gamma_tail/in_gamma_cons_gamma_head.
  apply: M=>//; apply/forces_gamma_cons_gamma_weak2/Fk=>F1 F2.
  apply: (forces_vimp2_t _ _ (Imp (Imp (Atom a) (Atom j)) c)
                             (Imp (Atom a) (Imp b (Atom j))))=>// k' S1 Fajc Fabj.
  rewrite /forces_t2 /= => k'' S2 S3 Fab.
  apply (Fajc k'')=>//  k''' S4 S5 Fa.
  apply: (Fabj k''' S4)=>//.
  - by apply/successor_trans/S3.
  - by apply: successor_refl.
  by apply: Fab.
- have Hja : j == a = false by move: Ha; rewrite lt_neqAle eq_sym; case/andP=>/negbTE.
  move=>D; apply/derivable/(derivable_cut _ (subst_form j b (vimp l (Imp (Atom a) (Imp b (Atom j)))))).
  - rewrite subst_vimp_head //= eqxx subst_form_below // Hja.
    rewrite (_ : vimp l (Imp (Atom a) (Imp b b)) = vimp (a::l) (Imp b b)) //.
    apply: derivable_vimp0=>ctx'.
    by apply/(Derivable_Intro _ _ (Abs b (Var 0)))/ImpIntro/ByAssumption.
  apply: (derivable_cut_merge _(subst_form j b (vimp l (Imp (Imp (Atom a) (Atom j)) c)))).
  - apply: derivable_weak; rewrite subst_vimp_head //= eqxx Hja (subst_form_below j b c) //.
    by apply/S/in_gamma_cons_gamma_head.
  rewrite -(subst_form_below j b goal) // -(subst_list_below j b ctx) //.
  rewrite (_ : [:: subst_form j b (vimp l (Imp (Imp (Atom a) (Atom j)) c)),
                   subst_form j b (vimp l (Imp (Atom a) (Imp b (Atom j)))) &
                   subst_list j b ctx] =
               subst_list j b [:: vimp l (Imp (Imp (Atom a) (Atom j)) c),
                                   vimp l (Imp (Atom a) (Imp b (Atom j))) &
                                   ctx]) //.
  by apply: derivable_subst.
move=>k Mk Fk Nk.
apply: (refutable _ _ _ _ k)=>//.
apply: (forces_gamma_cons_gamma_weak2 _ _ _ (vimp l (Imp (Imp (Atom a) (Atom j)) c))
                                            (vimp (a :: l) (Imp b (Atom j))))=>// F1 F2.
apply: (forces_vimp2_t _ _ (Imp (Imp (Atom a) (Atom j)) c)
                           (Imp (Atom a) (Imp b (Atom j))))=>// k' S1 Fajc Fabj.
rewrite /forces_t2 /= => k'' S2 S3 Fab.
apply (Fajc k'')=>//  k''' S4 S5 Fa.
apply: (Fabj k''' S4)=>//.
- by apply/successor_trans/S3.
- by apply: successor_refl.
by apply: Fab.
Qed.

Lemma rule_a_imp_b_imp_c_gamma goal l a b c gamma work ctx j j1 :
  j < j1 ->
  search_spec goal [:: vimp l (Imp (Imp (Atom j) b) c), Imp (Atom j) a & gamma] work
                   [:: vimp l (Imp (Imp (Atom j) b) c), Imp (Atom j) a & ctx] j1 ->
  search_spec goal (vimp l (Imp (Imp a b) c) :: gamma) work ctx j.
Proof.
move=>L S0.
apply: (search_spec_subst_gamma_pos _ _ _ _ _ j1 a (vimp l (Imp (Imp (Atom j) b) c)))=>//.
- move=>Bj.
  have H1 := below_vimp_tail _ _ _  Bj.
  move/implyP: (below_vimp_head j l (Imp (Imp a b) c))=>/(_ Bj) /=.
  rewrite -andbA => /and3P {Bj}[Ba Bb] Bc.
  have Bb1 : below_form b j1 by move: Bb; apply/implyP/less_below_form_imply.
  have Bc1 : below_form c j1 by move: Bc; apply/implyP/less_below_form_imply.
  split=>//.
  - move: (below_vimp_split j1 l (Imp (Imp (Atom j) b) c))=>/=.
    rewrite L Bb1 Bc1 /=; apply.
    by move=>k Hk; apply/lt_trans/L/H1.
  by rewrite (subst_vimp_head j l a (Imp (Imp (Atom j) b) c)) //= eqxx !subst_form_below.
move=>k Mk F1 F2.
apply: (forces_vimp_t _ _ (Imp (Imp (Atom j) b) c))=>//= k' S1 Fjbc.
rewrite /forces_t2 /= => k'' S2 S3 Fab.
apply: (Fjbc k'')=>// k''' S4 S5 Fj.
by apply: (Fab k''')=>//; apply: (F2 k''').
Qed.

End Rules.
