From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import forms normal_forms derivations kripke_trees
                           in_gamma forces_gamma derivable_def derivable_tools
                           sound minimal.

(*From ipcssr Require Import prelude avlmap forms normal_forms derivations kripke_trees
                           in_ngamma forces_ngamma derivable_def derivable_tools catrev le_ks
                           cons_counter_model disjunct ndeco_sound nsound nminimal.*)
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

(*
Lemma rule_gamma_a :
 forall (a : form) (gamma : flist) (work : nf_list)
   (ctx : flist) (j j1 : Int),
 Less j j1 ->
 search_spec (Atom j) (Imp a (Atom j) :: gamma) work
   (Imp a (Atom j) :: ctx) j1 -> search_spec a gamma work ctx j.
intros a gamma work ctx j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der.
clear minimal0 sound0.
apply derivable.
apply derivable_cut with (Imp a a).
apply derivable_a_imp_a.
apply
 derivable_eq
  with (subst_list j a (Imp a (Atom j) :: ctx)) (subst_form j a (Atom j)).
simpl in |- *.
 rewrite (subst_form_below j a a); try assumption.
 rewrite (subst_list_below j a ctx); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
simpl in |- *.
apply equal_dec_refl.
apply derivable_subst; assumption.
clear minimal0 sound0.
intros k k_is_mon k_forces_gamma k_notforces_j.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_tail with (Imp a (Atom j)); assumption.
intros forces_a.
apply k_notforces_j.
apply forces_a_a_imp_b__forces_b_t with a; try assumption.
apply forces_gamma_cons_gamma_head with gamma work; assumption.
apply below_cons_list.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply sound_cons_gamma_cons_context; assumption.
apply minimal_cons_gamma_cons_context; assumption.
Qed.


(***********************************************************************)
(***********************************************************************)


(*****************************************************)
(* rules for   ...(cons (vimp l (AndF a b)) gamma)... *)

Lemma rule_vimp_conj_gamma :
 forall (goal : form) (l : list Int) (b0 b1 : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j : Int),
 search_spec goal (vimp l b0 :: vimp l b1 :: gamma) work ctx j ->
 search_spec goal (vimp l (AndF b0 b1) :: gamma) work ctx j.
intros goal l b0 b1 gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak2 with (vimp l b0) (vimp l b1);
 try assumption.
intros forces_ab0 forces_ab1.
apply forces_vimp2 with b0 b1; try assumption.
intros; split; assumption.
apply below_list_weak2 with (vimp l (AndF b0 b1)); try assumption.
intros below_ab0b1.
split.
apply below_vimp with (AndF b0 b1); try assumption.
intros j' below_b0b1; elim below_b0b1; clear below_b0b1; intros; assumption.
apply below_vimp with (AndF b0 b1); try assumption.
intros j' below_b0b1; elim below_b0b1; clear below_b0b1; intros; assumption.
apply sound_cons_gamma_weak2 with (vimp l (AndF b0 b1)); try assumption.

intros der.
split.
apply derivable_vimp with (AndF b0 b1); try assumption.
intros ctx' der'.
apply (derivable_a_and_b__derivable_a b0 b1 ctx'); assumption.
apply derivable_vimp with (AndF b0 b1); try assumption.
intros ctx' der'.
apply (derivable_a_and_b__derivable_b b0 b1 ctx'); assumption.

apply minimal_cons_gamma_weak2 with (vimp l (AndF b0 b1)); try assumption.
intros k k_is_mon forces_b0 forces_b1.
apply forces_vimp2 with b0 b1; try assumption.
intros; split; assumption.
Qed.


Lemma rule_vimp_conj_gamma_new :
 forall (goal : form) (l : list Int) (b0 b1 : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp (j :: nil) b0 :: vimp (j :: nil) b1 :: gamma)
   (nvimp l (NAtom j) :: work)
   (vimp l (Atom j) :: Imp (Atom j) (AndF b0 b1) :: ctx) j1 ->
 search_spec goal (vimp l (AndF b0 b1) :: gamma) work ctx j.
intros goal l b0 b1 gamma work ctx j j1 less1 spec0.
apply rule_vimp_a_gamma with j1; try assumption.
apply rule_vimp_conj_gamma; assumption.
Qed.


(****************************************************)
(* rules for   ...(cons (vimp l (OrF a b)) gamma)... *)

Lemma rule_vimp_falsum_or_a_gamma :
 forall (goal : form) (l : list Int) (a : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j : Int),
 search_spec goal (vimp l a :: gamma) work ctx j ->
 search_spec goal (vimp l (OrF Falsum a) :: gamma) work ctx j.
intros goal l a gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros derivable_i; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l a); try assumption.
intros forces_la.
apply forces_vimp with a.
intros; right; assumption.
assumption.
apply below_list_weak with (vimp l (OrF Falsum a)); try assumption.
intros below_x.
apply below_vimp with (OrF Falsum a); try assumption.
intros j0 below_or; elim below_or; intros; assumption.
apply sound_cons_gamma_weak with (vimp l (OrF Falsum a)); try assumption.
intros der.
apply derivable_vimp with (OrF Falsum a); try assumption.
intros context0 der0.
apply derivable_falsum_or_a__derivable_a; assumption.
apply minimal_cons_gamma_weak with (vimp l (OrF Falsum a)); try assumption.
intros k k_is_mon k_forces_la.
apply forces_vimp with a; try assumption.
intros; right; assumption.
Qed.


Lemma rule_vimp_a_or_falsum_gamma :
 forall (goal : form) (l : list Int) (a : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j : Int),
 search_spec goal (vimp l a :: gamma) work ctx j ->
 search_spec goal (vimp l (OrF a Falsum) :: gamma) work ctx j.
intros goal l a gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros derivable_i; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l a); try assumption.
intros forces_la.
apply forces_vimp with a.
intros; left; assumption.
assumption.
apply below_list_weak with (vimp l (OrF a Falsum)); try assumption.
intros below_x.
apply below_vimp with (OrF a Falsum); try assumption.
intros j0 below_or; elim below_or; intros; assumption.
apply sound_cons_gamma_weak with (vimp l (OrF a Falsum)); try assumption.
intros der.
apply derivable_vimp with (OrF a Falsum); try assumption.
intros context0 der0.
apply derivable_a_or_falsum__derivable_a; assumption.
apply minimal_cons_gamma_weak with (vimp l (OrF a Falsum)); try assumption.
intros k k_is_mon k_forces_la.
apply forces_vimp with a; try assumption.
intros; left; assumption.
Qed.



Lemma rule_vimp_atom_or_a_gamma :
 forall (goal : form) (l : list Int) (i : Int) (a : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (Imp (Atom j) a :: gamma) (nvimp l (NDisj i j) :: work)
   (vimp l (OrF (Atom i) (Atom j)) :: Imp (Atom j) a :: ctx) j1 ->
 search_spec goal (vimp l (OrF (Atom i) a) :: gamma) work ctx j.
intros goal l i a gamma work ctx j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (OrF (Atom i) (Atom j)));
 try assumption.
intros below_c.
generalize (below_vimp_tail j l (OrF (Atom i) a) below_c).
generalize (below_vimp_head j l (OrF (Atom i) a) below_c); clear below_c.
intros below_c below_l; elim below_c; clear below_c; intros below_i below_a.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; try assumption.
assumption.
 rewrite (subst_vimp_head j a l (OrF (Atom i) (Atom j))); try assumption.
change
  (vimp l (OrF (subst_form j a (Atom i)) (subst_form j a (Atom j))) =
   vimp l (OrF (Atom i) a)) in |- *.
 rewrite (subst_form_below j a (Atom i)); try assumption.
simpl in |- *.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
intros k k_is_mon forces1 forces2.
apply forces_vimp with (OrF (Atom i) (Atom j)).
intros k' suc1 forces_ij.
elim forces_ij; clear forces_ij.
intros; left; assumption.
intros; right.
change (forces_t2 k k' a) in |- *.
apply (forces2 k'); assumption.
assumption.
apply rule_shift_gamma_work with (a := NDisj i j); assumption.
Qed.



Lemma rule_vimp_a_or_b_gamma :
 forall (goal : form) (l : list Int) (a b : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp l (OrF (Atom j) b) :: vimp (j :: nil) a :: gamma)
   work (vimp l (OrF (Atom j) b) :: Imp (Atom j) a :: ctx) j1 ->
 search_spec goal (vimp l (OrF a b) :: gamma) work ctx j.
intros goal l a b gamma work ctx j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (OrF (Atom j) b));
 try assumption; clear spec0.
intros below_c.
generalize (below_vimp_tail j l (OrF a b) below_c).
generalize (below_vimp_head j l (OrF a b) below_c); clear below_c.
intros below_ab below_l; elim below_ab; clear below_ab;
 intros below_a below_b.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
assumption.
apply below_form_less_below_form with j; try assumption.
 rewrite (subst_vimp_head j a l (OrF (Atom j) b)); try assumption.
simpl in |- *.
 rewrite (subst_form_below j a b); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.
intros k k_is_mon forces1 forces2.
apply forces_vimp with (OrF (Atom j) b).
intros k' suc1 forces_jb.
elim forces_jb; clear forces_jb.
intros; left.
change (forces_t2 k k' a) in |- *.
apply (forces2 k'); assumption.
intros; right; assumption.
assumption.
Qed.


(**********************************************************)
(* rules for   ...(cons (vimp l (Imp Falsum b)) gamma)... *)

Lemma rule_vimp_falsum_imp_b_gamma :
 forall (goal : form) (l : list Int) (b : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j : Int),
 search_spec goal gamma work ctx j ->
 search_spec goal (vimp l (Imp Falsum b) :: gamma) work ctx j.
intros goal l b gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma; try assumption.
apply forces_vimp0.
intros k' suc1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros; elimtype False; assumption.
apply below_cons_list_tail with (vimp l (Imp Falsum b)); assumption.
apply sound_cons_gamma_tail with (vimp l (Imp Falsum b)); assumption.
unfold minimal in |- *.
intros c k k_is_mon k_forces_gamma in_c.
apply minimal0; try assumption.
apply forces_gamma_cons_gamma; try assumption.
apply forces_vimp0.
intros k' suc1.
unfold forces_t in |- *; unfold forces_t2 in |- *; simpl in |- *.
intros; elimtype False; assumption.
Qed.

(**********************************************************)
(* rules for   ...(cons (vimp l (Imp (Atom i) b)) gamma)... *)

Lemma rule_vimp_atom_imp_b_gamma :
 forall (goal : form) (l : list Int) (i : Int) (b : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j : Int),
 search_spec goal (vimp (i :: l) b :: gamma) work ctx j ->
 search_spec goal (vimp l (Imp (Atom i) b) :: gamma) work ctx j.
intros; assumption.
Qed.


(*****************************************************)
(* rules for   ...(cons (Imp (AndF a0 a1) b) gamma)... *)

Lemma rule_vimp_and_imp_gamma :
 forall (goal : form) (l : list Int) (a0 a1 b : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j : Int),
 search_spec goal (vimp l (Imp a0 (Imp a1 b)) :: gamma) work ctx j ->
 search_spec goal (vimp l (Imp (AndF a0 a1) b) :: gamma) work ctx j.
intros goal l a0 a1 b gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp a0 (Imp a1 b)));
 try assumption.
intros forces_a0a1b.
apply forces_vimp with (Imp a0 (Imp a1 b)); try assumption.
intros k' suc1 forces1.
unfold forces_t2 in |- *;
 apply forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b;
 try assumption.
apply kripke_tree_kripke_model; assumption.
apply below_list_weak with (vimp l (Imp (AndF a0 a1) b)); try assumption.
intros below_lab.
apply below_vimp with (Imp (AndF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split.
assumption.
split; assumption.
apply sound_cons_gamma_weak with (vimp l (Imp (AndF a0 a1) b));
 try assumption.
intros der.
apply derivable_vimp with (Imp (AndF a0 a1) b); try assumption.
intros ctx' der'.
apply derivable_a0_and_a1_imp_b__derivable_a0_imp_a1_imp_b; assumption.
apply minimal_cons_gamma_weak with (vimp l (Imp (AndF a0 a1) b));
 try assumption.
intros k k_is_mon forces1.
apply forces_vimp with (Imp a0 (Imp a1 b)); try assumption.
intros k' suc1 forces'.
unfold forces_t2 in |- *;
 apply forces_a0_imp_a1_imp_b__forces_a0_and_a1_imp_b;
 try assumption.
apply kripke_tree_kripke_model; assumption.
Qed.


(**************************************************************)
(* rules for   ...(cons (vimp l (Imp (OrF a0 a1) b)) gamma)... *)


Lemma rule_vimp_or_imp_gamma :
 forall (goal : form) (l : list Int) (a0 a1 b : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j : Int),
 search_spec goal (vimp l (Imp a0 b) :: vimp l (Imp a1 b) :: gamma) work
   ctx j ->
 search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work ctx j.
intros goal l a0 a1 b gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply
 forces_gamma_cons_gamma_weak2 with (vimp l (Imp a0 b)) (vimp l (Imp a1 b));
 try assumption.
intros forces1 forces2.
apply forces_vimp2 with (Imp a0 b) (Imp a1 b); try assumption.
intros k' suc1 forces_a0b forces_a1b.
unfold forces_t2 in |- *;
 apply forces_a0_imp_b_and_a1_imp_b__forces_a0_or_a1_imp_b;
 try assumption.
apply below_list_weak2 with (vimp l (Imp (OrF a0 a1) b)); try assumption.
intros below1.
split.
apply below_vimp with (Imp (OrF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split; assumption.
apply below_vimp with (Imp (OrF a0 a1) b); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
elim below_a; clear below_a; intros below_a0 below_a1.
split; assumption.
apply sound_cons_gamma_weak2 with (vimp l (Imp (OrF a0 a1) b));
 try assumption.
intros der.
split.
apply derivable_vimp with (Imp (OrF a0 a1) b); try assumption.
intros ctx' der'.
apply (derivable_a0_or_a1_imp_b__derivable_a0_imp_b ctx' a0 a1 b der');
 assumption.
apply derivable_vimp with (Imp (OrF a0 a1) b); try assumption.
intros ctx' der'.
apply (derivable_a0_or_a1_imp_b__derivable_a1_imp_b ctx' a0 a1 b der');
 assumption.

apply minimal_cons_gamma_weak2 with (vimp l (Imp (OrF a0 a1) b));
 try assumption.
intros k k_is_mon forces1 forces2.
apply forces_vimp2 with (Imp a0 b) (Imp a1 b); try assumption.
intros k' suc1 forces_a0b forces_a1b.
unfold forces_t2 in |- *;
 apply forces_a0_imp_b_and_a1_imp_b__forces_a0_or_a1_imp_b;
 try assumption.
Qed.



Lemma rule_vimp_or_imp_gamma_new :
 forall (goal : form) (l : list Int) (a0 a1 b : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp a0 (Atom j))
    :: vimp l (Imp a1 (Atom j)) :: vimp (j :: nil) b :: gamma) work
   (vimp l (Imp (OrF a0 a1) (Atom j)) :: Imp (Atom j) b :: ctx) j1 ->
 search_spec goal (vimp l (Imp (OrF a0 a1) b) :: gamma) work ctx j.
intros goal l a0 a1 b gamma work ctx j j1 less1 spec0.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_vimp_or_imp_gamma; assumption.
Qed.



(*************************************************************)
(* rules for   ...(cons (vimp l (Imp (Imp a b) c)) gamma)... *)


Lemma rule_vimp_falsum_imp_imp_gamma :
 forall (goal : form) (l : list Int) (b c : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j : Int),
 search_spec goal (vimp l c :: gamma) work ctx j ->
 search_spec goal (vimp l (Imp (Imp Falsum b) c) :: gamma) work ctx j.
intros goal l b c gamma work ctx j spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
elim spec0; clear spec0; try assumption.
intros der_goal; apply derivable; assumption.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l c); try assumption.
intros forces_lc.
apply forces_vimp with c; try assumption.
intros.
unfold forces_t2 in |- *; apply forces_b__forces_a_imp_b; try assumption.
apply kripke_tree_kripke_model; assumption.
apply below_list_weak with (vimp l (Imp (Imp Falsum b) c)); try assumption.
intros below_lc.
apply below_vimp with (Imp (Imp Falsum b) c); try assumption.
intros j' below_ab; elim below_ab; clear below_ab; intros below_a below_b.
assumption.
apply sound_cons_gamma_weak with (vimp l (Imp (Imp Falsum b) c));
 try assumption.
intros der.
apply derivable_vimp with (Imp (Imp Falsum b) c).
intros ctx' der'.
apply derivable_falsum_imp_b_imp_c__derivable_c with b; assumption.
assumption.
apply minimal_cons_gamma_weak with (vimp l (Imp (Imp Falsum b) c));
 try assumption.
intros k k_is_mon forces1.
apply forces_vimp with c; try assumption.
intros.
unfold forces_t2 in |- *; apply forces_b__forces_a_imp_b; try assumption.
apply kripke_tree_kripke_model; assumption.
Qed.


Lemma rule_vimp_imp_falsum_imp_gamma :
 forall (goal : form) (l : list Int) (a c : form) (gamma : flist)
   (work : nf_list) (ctx : flist) (j j1 : Int),
 Less j j1 ->
 search_spec goal (vimp l (Imp (Imp a (Atom j)) c) :: gamma) work
   (vimp l (Imp (Imp a (Atom j)) c) :: ctx) j1 ->
 search_spec goal (vimp l (Imp (Imp a Falsum) c) :: gamma) work ctx j.
intros goal l a c gamma work ctx j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
generalize
 (below_cons_list_head (vimp l (Imp (Imp a Falsum) c)) gamma j below_gamma).
intros below_lc.
generalize
 (below_cons_list_tail (vimp l (Imp (Imp a Falsum) c)) gamma j below_gamma).
clear below_gamma; intros below_gamma.
elim (below_vimp_head j l (Imp (Imp a Falsum) c) below_lc).
intros below_a_falsum; elim below_a_falsum; clear below_a_falsum.
intros below_a below_falsum below_c.
generalize (below_vimp_tail j l (Imp (Imp a Falsum) c) below_lc);
 clear below_lc.
intros below_l.
elim spec0; clear spec0; try assumption.
clear minimal0.
intros der_goal.
apply derivable.
apply derivable_cut_merge with (vimp l (Imp (Imp a Falsum) c)).
apply sound0.
apply in_gamma_cons_gamma_head.
apply
 derivable_eq
  with
    (subst_list j Falsum (vimp l (Imp (Imp a (Atom j)) c) :: ctx))
    (subst_form j Falsum goal).
simpl in |- *.
 rewrite (subst_vimp_head j Falsum l (Imp (Imp a (Atom j)) c)).
simpl in |- *.
 rewrite (subst_form_below j Falsum a); try assumption.
 rewrite (subst_form_below j Falsum c); try assumption.
 rewrite (equal_dec_refl j form Falsum (Atom j)).
 rewrite (subst_list_below j Falsum ctx); try assumption.
trivial.
assumption.
apply subst_form_below; assumption.
apply derivable_subst; assumption.
clear minimal0.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp (Imp a (Atom j)) c));
 try assumption.
intros forces_lc.
apply forces_vimp with (Imp (Imp a (Atom j)) c); try assumption.
intros k' suc1 forces1.
apply forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c_t2 with (Atom j);
 assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0.
apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_list_less_below_list with j; assumption.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_tail with (vimp l (Imp (Imp a Falsum) c)); assumption.
unfold minimal in |- *.
intros x k k_is_mon k_forces_gamma in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_head.
apply minimal0; try assumption; clear H.
apply forces_gamma_cons_gamma_weak with (vimp l (Imp (Imp a (Atom j)) c));
 try assumption.
intros forces1.
apply forces_vimp with (Imp (Imp a (Atom j)) c); try assumption.
intros k' suc1 forces2.
apply forces_a_imp_b_imp_c__forces_a_imp_falsum_imp_c_t2 with (Atom j);
 assumption.
Qed.


Lemma rule_atom_imp_atom_imp_c_gamma :
 forall (goal : form) (l : list Int) (a b : Int) (c : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal (Imp (Atom j) c :: gamma)
   (nvimp l (NImp_NF (NImp a b (NAtom j))) :: work)
   (vimp l (Imp (Imp (Atom a) (Atom b)) (Atom j))
    :: Imp (Atom j) c :: ctx) j1 ->
 search_spec goal (vimp l (Imp (Imp (Atom a) (Atom b)) c) :: gamma) work
   ctx j.
intros goal l a b c gamma work ctx j j1 less1 spec0.
apply rule_vimp_imp_gamma with j1; try assumption.
apply rule_shift_gamma_work with (a := NImp_NF (NImp a b (NAtom j)));
 assumption.
Qed.


Lemma rule_atom_imp_b_imp_c_gamma :
 forall (goal : form) (l : list Int) (a : Int) (b c : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp (Imp (Atom a) (Atom j)) c)
    :: vimp (a :: l) (Imp b (Atom j)) :: gamma) work
   (vimp l (Imp (Imp (Atom a) (Atom j)) c)
    :: vimp (a :: l) (Imp b (Atom j)) :: ctx) j1 ->
 search_spec goal (vimp l (Imp (Imp (Atom a) b) c) :: gamma) work ctx j.
intros goal l a b c gamma work ctx j j1 less1 spec0.
unfold search_spec in |- *.
intros below_goal below_gamma below_context sound0 minimal0.
generalize
 (below_cons_list_head (vimp l (Imp (Imp (Atom a) b) c)) gamma j below_gamma).
generalize
 (below_cons_list_tail (vimp l (Imp (Imp (Atom a) b) c)) gamma j below_gamma);
 clear below_gamma.
intros below_gamma below_x.
generalize (below_vimp_head j l (Imp (Imp (Atom a) b) c) below_x).
generalize (below_vimp_tail j l (Imp (Imp (Atom a) b) c) below_x);
 clear below_x.
intros below_l below_x.
elim below_x; clear below_x; intros below_x below_c.
elim below_x; clear below_x; intros below_a below_b.
elim spec0; clear spec0; try assumption.
clear minimal0.
intros derivable_i.
apply derivable.
apply
 derivable_cut with (subst_form j b (vimp l (Imp (Atom a) (Imp b (Atom j))))).
 rewrite (subst_vimp_head j b l (Imp (Atom a) (Imp b (Atom j))));
 try assumption.
simpl in |- *.
 rewrite (subst_form_below j b b); try assumption.
 rewrite (equal_dec_refl j form b (Atom j)).
change (Derivable fnil (vimp l (Imp (subst_form j b (Atom a)) (Imp b b))))
 in |- *.
 rewrite (subst_form_below j b (Atom a)); try assumption.
change (Derivable fnil (vimp (a :: l) (Imp b b))) in |- *.
apply derivable_vimp0.
intros.
apply Derivable_Intro with (Abs b (Var 0)).
apply ImpIntro.
apply ByAssumption.
apply My_NthO.
apply
 derivable_cut_merge
  with (subst_form j b (vimp l (Imp (Imp (Atom a) (Atom j)) c))).
apply derivable_weak.
 rewrite (subst_vimp_head j b l (Imp (Imp (Atom a) (Atom j)) c));
 try assumption.
simpl in |- *.
 rewrite (subst_form_below j b c); try assumption.
 rewrite (equal_dec_refl j form b (Atom j)).
change (Derivable ctx (vimp l (Imp (Imp (subst_form j b (Atom a)) b) c)))
 in |- *.
 rewrite (subst_form_below j b (Atom a)); try assumption.
apply sound0.
apply in_gamma_cons_gamma_head.
 rewrite <- (subst_form_below j b goal); try assumption.
 rewrite <- (subst_list_below j b ctx); try assumption.
change
  (Derivable
     (subst_list j b
        (vimp l (Imp (Imp (Atom a) (Atom j)) c)
         :: vimp l (Imp (Atom a) (Imp b (Atom j))) :: ctx))
     (subst_form j b goal)) in |- *.
apply derivable_subst; assumption.
clear minimal0 sound0 below_context below_gamma below_goal.
intros k k_is_mon k_forces_gamma k_notforces_goal.
apply refutable with k; try assumption.
apply
 forces_gamma_cons_gamma_weak2
  with
    (vimp l (Imp (Imp (Atom a) (Atom j)) c))
    (vimp (a :: l) (Imp b (Atom j))); try assumption.
intros forces1 forces2.
apply
 forces_vimp2
  with (Imp (Imp (Atom a) (Atom j)) c) (Imp (Atom a) (Imp b (Atom j)));
 try assumption.
intros k' suc1 forces_ajc forces_abj.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp (Atom a) b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_ajc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom a) -> forces_t2 k k''' (Atom j)) in |- *.
intros forces_a.
generalize (forces_abj k''' suc4).
simpl in |- *.
fold forces in |- *.
clear forces_abj; intros forces_abj.
unfold forces_t2 in |- *.
simpl in |- *.
apply forces_abj; try assumption.
unfold Suc in |- *; apply succs_trans with k''; try assumption.
unfold Suc in |- *; apply successor_refl.
apply forces_ab; try assumption.


clear minimal0 sound0.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0; apply less_trans with j.
apply below_l; assumption.
assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
simpl in |- *.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; assumption.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.
apply below_cons_list.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_cons_list.
simpl in |- *.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
apply below_form_less_below_form with j; assumption.
split.
apply below_form_less_below_form with j; assumption.
assumption.
apply below_list_less_below_list with j; assumption.

clear minimal0 below_context below_gamma below_goal.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_cons_context.
apply sound_cons_gamma_tail with (vimp l (Imp (Imp (Atom a) b) c));
 assumption.
clear sound0 below_context below_gamma below_goal below_b below_a.

unfold minimal in |- *.
intros x k k_is_mon k_forces_gamma in_x.
inversion_clear in_x.
 rewrite <- H; clear H x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_head.
inversion_clear H.
 rewrite <- H0; clear H0 x.
apply k_forces_gamma.
apply in_gamma_cons_gamma_tail.
apply in_gamma_cons_gamma_head.
apply minimal0; try assumption.
clear H0 x.
apply
 forces_gamma_cons_gamma_weak2
  with
    (vimp l (Imp (Imp (Atom a) (Atom j)) c))
    (vimp (a :: l) (Imp b (Atom j))); try assumption.
intros forces1 forces2.
apply
 forces_vimp2
  with (Imp (Imp (Atom a) (Atom j)) c) (Imp (Atom a) (Imp b (Atom j)));
 try assumption.
intros k' suc1 forces_ajc forces_abj.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp (Atom a) b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_ajc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom a) -> forces_t2 k k''' (Atom j)) in |- *.
intros forces_a.
generalize (forces_abj k''' suc4).
simpl in |- *.
fold forces in |- *.
clear forces_abj; intros forces_abj.
unfold forces_t2 in |- *.
simpl in |- *.
apply forces_abj; try assumption.
unfold Suc in |- *; apply succs_trans with k''; try assumption.
unfold Suc in |- *; apply successor_refl.
apply forces_ab; try assumption.
Qed.





Lemma rule_a_imp_b_imp_c_gamma :
 forall (goal : form) (l : list Int) (a b c : form)
   (gamma : flist) (work : nf_list) (ctx : flist)
   (j j1 : Int),
 Less j j1 ->
 search_spec goal
   (vimp l (Imp (Imp (Atom j) b) c) :: Imp (Atom j) a :: gamma) work
   (vimp l (Imp (Imp (Atom j) b) c) :: Imp (Atom j) a :: ctx) j1 ->
 search_spec goal (vimp l (Imp (Imp a b) c) :: gamma) work ctx j.
intros goal l a b c gamma work ctx j j1 less1 spec0.
apply
 search_spec_subst_gamma_pos
  with (j1 := j1) (a := a) (b := vimp l (Imp (Imp (Atom j) b) c));
 try assumption; clear spec0.
intros below_x.
generalize (below_vimp_tail j l (Imp (Imp a b) c) below_x).
generalize (below_vimp_head j l (Imp (Imp a b) c) below_x); clear below_x.
intros below_x below_l.
elim below_x; clear below_x; intros below_ab below_c.
elim below_ab; clear below_ab; intros below_a below_b.
split.
assumption.
split.
apply below_vimp_split.
intros i0 in0; apply less_trans with j; try assumption.
apply below_l; assumption.
split.
split.
assumption.
apply below_form_less_below_form with j; assumption.
apply below_form_less_below_form with j; assumption.
 rewrite (subst_vimp_head j a l (Imp (Imp (Atom j) b) c)); try assumption.
simpl in |- *.
 rewrite (subst_form_below j a b); try assumption.
 rewrite (subst_form_below j a c); try assumption.
 rewrite (equal_dec_refl j form a (Atom j)).
trivial.

intros k k_is_mon forces1 forces2.
apply forces_vimp with (Imp (Imp (Atom j) b) c); try assumption.
intros k' suc1 forces_jbc.
unfold forces_t2 in |- *; simpl in |- *.
intros k'' suc2 suc3.
change (forces_t2 k k'' (Imp a b) -> forces_t2 k k'' c) in |- *.
intros forces_ab.
apply (forces_jbc k''); try assumption.
intros k''' suc4 suc5.
change (forces_t2 k k''' (Atom j) -> forces_t2 k k''' b) in |- *.
intros forces_j.
apply (forces_ab k'''); try assumption.
change (forces_t2 k k''' a) in |- *.
apply (forces2 k'''); assumption.
Qed.
*)

End Rules.

From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Set Extraction Flag 522.
Extract Inlined Constant negb => "not".
Extract Inlined Constant idP => "".
Extract Inlined Constant eqn => "equal".  (* ints! *)
Extract Inlined Constant size => "List.length".
Extract Inlined Constant cat => "List.append".
Extract Inductive reflect => bool [ true false ].
Extract Inductive alt_spec => bool [ true false ].
Extract Inductive eq_xor_neq => bool [ true false ].
Extract Inductive leq_xor_gtn => bool [ true false ].
Extract Inductive ltn_xor_geq => bool [ true false ].

Extraction "ext.ml" rule_shift_gamma_work search_spec_subst_gamma_pos
                    rule_vimp_a_gamma rule_vimp_imp_gamma
                    rule_gamma_falsum rule_gamma_a_imp_b.