From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq eqtype order.
From ipcssr Require Import prelude avlmap forms normal_forms trees kripke_trees
                           in_ngamma forces_ngamma disjunct ndeco_sound catrev.

Section ConsCounterModel.
Context {disp : unit} {A : orderType disp}.

Fixpoint n2forest (n : seq (nested_imp A)) : seq (kripke_tree A) :=
  match n with
  | [::] => [::]
  | Undecorated _ :: n => n2forest n
  | Decorated _ k :: n => k :: n2forest n
  end.

Remark cons_counter_model_suc x k ni a :
  Decorated x k \in ni -> Suc k (TNode a (n2forest ni)).
Proof.
move=>D /=; apply/orP; right.
elim: ni D=>//= n ni IH; rewrite inE; case/orP=>[/eqP<-|D] /=.
- by apply/orP; left; apply: successor_refl.
case: n=>[y|y q] /=.
- by apply: IH.
by rewrite IH // orbT.
Qed.

Remark in_forest_ex_a0a1b (k : kripke_tree A) ni :
  k \in n2forest ni -> exists x, Decorated x k \in ni.
Proof.
elim: ni=>//= n ni IH.
case: n=>[y|y q].
- by case/IH=>z Hz; exists z; rewrite inE.
rewrite inE; case/orP=>[/eqP{q}<-|H].
- by exists y; rewrite inE eqxx.
by case: (IH H)=>z Hz; exists z; rewrite inE Hz orbT.
Qed.

(**********************************************************************)

Remark deco_sound_in_forest_forces work ds ni ai a k c :
  deco_sound work ds ni ai a ->
  k \in n2forest ni ->
  in_ngamma work ds ni ai a c -> forces_t k (nf2form c).
Proof.
move=>D + H; case/in_forest_ex_a0a1b; case=>a0 a1 b Hi.
by case: (D _ _ _ _ Hi)=>_ + _; apply.
Qed.

(**********************************************************************)

Remark cons_counter_model_mon ni ai a :
  (forall x, Undecorated x \notin ni) ->
  deco_sound [::] [::] ni ai a ->
  Is_Monotone_kripke_tree (TNode a (n2forest ni)).
Proof.
elim: ni=>//=; case=>/=.
- by move=>x ni _ /(_ x); rewrite inE eqxx.
case=>a0 a1 b k ni IH H D.
case: (D k a0 a1 b); first by rewrite inE eqxx.
move=>M F _; do!split=>//=.
- move=>i; apply/implyP=>L.
  by apply/(F (NAtom i))/In_Atoms.
apply: IH; first by move=>x; move: (H x); rewrite inE.
by apply/deco_sound_cons_ni_tail/D.
Qed.

(**********************************************************************)

Definition Cons_Counter_Model_Spec (goal : A) (ni : (seq (nested_imp A)))
                                   (ai : atomic_imps A) (a : atoms A) : Type :=
  {k : kripke_tree A | [/\ Is_Monotone_kripke_tree k,
                           forces_ngamma [::] [::] ni ai a k &
                           ~ forces_t k (Atom goal)] }.

Lemma cons_counter_model i dni ai a :
  deco_sound [::] [::] (rev_d dni) ai a ->
  a_ai_disj a ai -> a_goal_disj a i ->
  Cons_Counter_Model_Spec i (rev_d dni) ai a.
Proof.
move=>D Aa Ad.
have M: Is_Monotone_kripke_tree (TNode a (n2forest (rev_d dni))).
- apply: (cons_counter_model_mon _ ai)=>// x.
  by exact: undec_nmem.
exists (TNode a (n2forest (rev_d dni))); split=>//; last by apply/negP.
rewrite /forces_ngamma => c; case=>{c} //=.
- move=>n [a0 a1 b] E.
  have En : nf2form (NImp_NF (NImp a0 a1 b)) = Imp (Imp (Atom a0) (Atom a1)) (nf2form b) by [].
  rewrite En; apply: forces_t_imp=>//.
  - move=>H; exfalso; move: E; rewrite onth_map.
    case E: (onth (rev_d dni) n) =>[z|] //= [].
    case: z E=>[z|z k].
    - by move: (undec_nmem dni z)=>/[swap]/onth_mem->.
    move=>E E'; case: (D k a0 a1 b).
    - by rewrite -E' /=; apply/onth_mem/E.
    move=>{E'} _ _; apply; apply/forces_t_mon/H=>//.
    by apply/(cons_counter_model_suc z)/onth_mem/E.
  move=>/= k Hk; rewrite -En.
  apply: (deco_sound_in_forest_forces [::] [::] (rev_d dni) ai a)=>//.
  by apply: (In_Nested_Imps _ _ _ _ _ n).
move=>j b n bs E Eo; have En: nf2form (AImp j b) = Imp (Atom j) (nf2form b) by [].
rewrite En; apply: forces_t_imp=>//=.
- move=>F; exfalso.
  by move/negP: (Aa _ F); apply; apply/optP; exists bs.
move=>k Hk; rewrite -En.
apply: (deco_sound_in_forest_forces [::] [::] (rev_d dni) ai a)=>//.
by apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
Qed.

End ConsCounterModel.
