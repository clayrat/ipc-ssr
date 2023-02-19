From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import prelude avlmap trees forms normal_forms kripke_trees.

(*******************************************************************)
(* The left hand side Gamma of a sequent consists of               *)
(*     work : a list of (arbitrary) normal forms                   *)
(*            (to be inserted in the following structures)         *)
(*     ds: a list of disjunctions                                  *)
(*     ni: a list of decorated and undecorated nested implications *)
(*     ai: an AVL tree of atomic implications                      *)
(*     a: an AVL tree of atoms                                     *)
(*******************************************************************)

Section In_NGamma.
Context {disp : unit}.

Definition disj A := (A * A)%type.

Definition disj2form {A} (d : disj A) :=
  let: (i, j) := d in
    OrF (Atom i) (Atom j).

(*****************************************************************)
(* Nested implications are stored either as a nimp or as a       *)
(* nimp and a counter-model                                      *)

Variant nested_imp (A : orderType disp) :=
                       Undecorated of nimp A
                     | Decorated of nimp A & kripke_tree A.

Definition eqnestedimp {A} (ni1 ni2 : nested_imp A) : bool :=
  match ni1, ni2 with
  | Undecorated n1,  Undecorated n2   => n1 == n2
  | Decorated n1 k1, Decorated n2 k2 => (n1 == n2) && (k1 == k2)
  | _, _ => false
  end.

Lemma eqnestedimpP {A} : Equality.axiom (@eqnestedimp A).
Proof.
case=>[n1|n1 k1]; case=>[n2|n2 k2] /=; try by constructor.
- by have [<-/=|N] := n1 =P n2; constructor=>//; case.
have [<-/=|N] := n1 =P n2; last by constructor; case.
by have [<-/=|Nk] := k1 =P k2; constructor=>//; case.
Qed.

Canonical nested_imp_eqMixin {A} := EqMixin (@eqnestedimpP A).
Canonical nested_imp_eqType {A} := Eval hnf in EqType (nested_imp A) nested_imp_eqMixin.

Definition nested_imp2nimp {A} (ni : nested_imp A) :=
  match ni with
  | Undecorated ni => ni
  | Decorated ni _ => ni
  end.

Definition nested_imp2form {A} (ni : nested_imp A) := nimp2form (nested_imp2nimp ni).

(************************************************************************)
(* Atomic implications are stored in AVL Trees ai over lists of normal  *)
(* clauses.                                                             *)
(* For the node with the key field=i and with the data field=bs,        *)
(* we define that, for each b in bs, (Imp (Atom i) b) is in ai.         *)
(************************************************************************)

Definition atomic_imps (A : orderType disp) := kvtree A (seq (normal_form A)).

Context {A : orderType disp}.

(************************************************************************)
(* The formulae on the left-hand side of the sequent are given by:      *)

Inductive in_ngamma (work : seq (normal_form A)) (ds : seq (disj A)) (ni : seq (nested_imp A))
                    (ai : atomic_imps A) (a : atoms A) : normal_form A -> Type :=
  | In_Work n c :
      onth work n = Some c ->
      in_ngamma work ds ni ai a c
  | In_Disjs n i j :
      onth ds n = Some (i, j) ->
      in_ngamma work ds ni ai a (NDisj i j)
  | In_Nested_Imps n x :
      onth (map nested_imp2nimp ni) n = Some x ->
      in_ngamma work ds ni ai a (NImp_NF x)
  | In_Atomic_Imps i b n bs :
      lookup ai i = Some bs -> onth bs n = Some b ->
      in_ngamma work ds ni ai a (AImp i b)
  | In_Atoms i :
      lookup a i -> in_ngamma work ds ni ai a (NAtom i).

(* proof-relevant lemmas follow *)

Lemma in_ngamma_cons_work_tail c0 work ds ni ai a c :
  in_ngamma work ds ni ai a c -> in_ngamma (c0 :: work) ds ni ai a c.
Proof.
case=>{c}.
- by move=>n c1 H; apply: (In_Work _ _ _ _ _ n.+1).
- by move=>n i j H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>i b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>i H; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_work_head c work ds ni ai a :
  in_ngamma (c :: work) ds ni ai a c.
Proof. by apply: (In_Work _ _ _ _ _ 0). Qed.

Lemma in_ngamma_work_catl bs work ds ni ai a c :
  in_ngamma work ds ni ai a c -> in_ngamma (bs ++ work) ds ni ai a c.
Proof.
case=>{c}.
- move=>n c H; apply: (In_Work _ _ _ _ _ (size bs + n)).
  by rewrite onth_cat ltnNge leq_addr /= addKn.
- by move=>n i j H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>i b n bs0 H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs0).
by move=>i H; apply: In_Atoms.
Qed.

Lemma in_ngamma_work_cat_rev bs work ds ni ai a c :
  in_ngamma (bs ++ work) ds ni ai a c ->
  in_ngamma work ds ni ai a c + {n : nat | onth bs n = Some c}.
Proof.
case=>{c}.
- move=>n c; rewrite onth_cat.
  case: (ltnP n (size bs))=>Hn H; first by right; exists n.
  by left; apply: (In_Work _ _ _ _ _ (n - size bs)).
- by move=>n i j H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>i b n bs0 H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs0).
by move=>i H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_work_rev c0 work ds ni ai a c :
  in_ngamma (c0 :: work) ds ni ai a c ->
  in_ngamma work ds ni ai a c + {c = c0}.
Proof.
case=>{c}.
- move=>+ c; case=>/= [[->]|n H]; first by right.
  by left; apply: (In_Work _ _ _ _ _ n).
- by move=>n i j H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>i b n bs0 H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs0).
by move=>i H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_ds_tail work i j ds ni ai a c :
 in_ngamma work ds ni ai a c -> in_ngamma work ((i, j) :: ds) ni ai a c.
Proof.
case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n k h H; apply: (In_Disjs _ _ _ _ _ n.+1).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>k b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_ds_head work i j ds ni ai a :
  in_ngamma work ((i, j) :: ds) ni ai a (NDisj i j).
Proof. by apply: (In_Disjs _ _ _ _ _ 0). Qed.

Lemma in_ngamma_cons_ds_rev work i j ds ni ai a c :
  in_ngamma work ((i, j) :: ds) ni ai a c ->
  in_ngamma work ds ni ai a c + {c = NDisj i j}.
Proof.
case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- case=>[|n] k h /=.
  - by case=>->->; right.
  by move=>H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>k b n bs H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>k H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_ni_tail work ds x ni ai a c :
  in_ngamma work ds ni ai a c ->
  in_ngamma work ds (x :: ni) ai a c.
Proof.
case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n k h H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n ni1 H; apply: (In_Nested_Imps _ _ _ _ _ n.+1).
- by move=>i b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_cons_ni_head work ds x ni ai a :
  in_ngamma work ds (x :: ni) ai a (NImp_NF (nested_imp2nimp x)).
Proof. by apply: (In_Nested_Imps _ _ _ _ _ 0). Qed.

Lemma in_ngamma_cons_ni_rev work ds x ni ai a c :
  in_ngamma work ds (x :: ni) ai a c ->
  in_ngamma work ds ni ai a c + {c = NImp_NF (nested_imp2nimp x)}.
Proof.
case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- by move=>n i j H; left; apply: (In_Disjs _ _ _ _ _ n).
- case=>[|n] x0 /=.
  - by case=>[->]; right.
  by move=>H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>i b n bs H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>i H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_ni_x_ni_head work ds x ni1 ni2 ai a :
  in_ngamma work ds (ni1 ++ x :: ni2) ai a (NImp_NF (nested_imp2nimp x)).
Proof.
apply: (In_Nested_Imps _ _ _ _ _ (size ni1)).
by rewrite map_cat /= onth_cat /= size_map ltnn subnn.
Qed.

Lemma in_ngamma_ni_x_ni_tail work ds x ni1 ni2 ai a c :
  in_ngamma work ds (ni1 ++ ni2) ai a c ->
  in_ngamma work ds (ni1 ++ x :: ni2) ai a c.
Proof.
case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n i j H; apply: (In_Disjs _ _ _ _ _ n).
- move=>n x0.
  rewrite map_cat /= onth_cat /= size_map.
  case: (ltnP n (size ni1))=>Hn H.
  - apply: (In_Nested_Imps _ _ _ _ _ n).
    by rewrite map_cat /= onth_cat /= size_map Hn.
  apply: (In_Nested_Imps _ _ _ _ _ n.+1).
  by rewrite map_cat /= onth_cat /= size_map ltnNge leq_eqVlt ltnS Hn orbT /= subSn.
- by move=>i b n bs0 H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs0).
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_ni_x_ni_rev work ds x ni1 ni2 ai a c :
  in_ngamma work ds (ni1 ++ x :: ni2) ai a c ->
  in_ngamma work ds (ni1 ++ ni2) ai a c + {c = NImp_NF (nested_imp2nimp x)}.
Proof.
case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- by move=>n i j H; left; apply: (In_Disjs _ _ _ _ _ n).
- move=>n x0.
  rewrite map_cat /= onth_cat /= size_map.
  case: (ltngtP n (size ni1)).
  - move=>Hn H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
    by rewrite map_cat onth_cat size_map Hn.
  - move/[dup]=>Hn; rewrite -subn_gt0 => Hn'.
    rewrite -(ltn_predK Hn')=>H.
    left; apply: (In_Nested_Imps _ _ _ _ _ n.-1).
    rewrite map_cat onth_cat size_map.
    by rewrite (ltn_predK Hn) leqNgt Hn /= -predn_sub.
  by move=>->; rewrite subnn; case=>->; right.
- by move=>i b n bs H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>i H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_ni_eq work ds ni ni' ai a c :
  map nested_imp2nimp ni = map nested_imp2nimp ni' ->
  in_ngamma work ds ni ai a c -> in_ngamma work ds ni' ai a c.
Proof.
move=>E; case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n i j H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n); rewrite -E.
- by move=>i b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_ins_ai_tail work ds ni i b ai a c :
  invariant ai ->
  in_ngamma work ds ni ai a c ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a c.
Proof.
move=>Ha; case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- move=>j b0 n bs H1 H2.
  case: (eqVneq j i)=>[<-|N].
  - apply: (In_Atomic_Imps _ _ _ _ _ _ _ n.+1 (b::bs))=>//.
    by rewrite lookup_upsert //= eqxx /= H1.
  apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs)=>//.
  by rewrite lookup_upsert //= (negbTE N).
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_ins_ai_head_new work ds ni i b ai a :
  invariant ai -> ~~ lookup ai i ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a (AImp i b).
Proof.
move=>Ha H; apply: (In_Atomic_Imps _ _ _ _ _ _ _ 0 [::b])=>//=.
by rewrite lookup_upsert //= eqxx; move/negOptP: H=>->.
Qed.

Lemma in_ngamma_ins_ai_head_old work ds ni i b bs ai a :
  invariant ai -> lookup ai i = Some bs ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a (AImp i b).
Proof.
move=>Ha H; apply: (In_Atomic_Imps _ _ _ _ _ _ _ 0 (b::bs))=>//=.
by rewrite lookup_upsert //= eqxx H.
Qed.

Lemma in_ngamma_ins_ai_rev work ds ni i b ai a c :
  invariant ai ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a c ->
  in_ngamma work ds ni ai a c + {c = AImp i b}.
Proof.
move=>Ha; case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- move=>j b0 n bs; rewrite lookup_upsert //=; case: (eqVneq j i)=>[{j}->|N].
  - case: n=>[|n].
    - by case: (lookup ai i)=>[x|]/= [<-] /= [<-]; right.
    move=>H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n (behead bs)).
    - case: (lookup ai i) H1=>[x|]/= [E]; first by rewrite -E.
      by rewrite -E in H2.
    by case: {H1}bs H2.
  by move=>H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
by move=>k H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_del_ai_tail work ds ni i ai a c :
  invariant ai ->
  in_ngamma work ds ni (delete i ai) a c ->
  in_ngamma work ds ni ai a c.
Proof.
move=>Ha; case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- move=>j b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs)=>//.
  by move: H1; rewrite lookup_delete=>//=; case: eqP.
by move=>k H; apply: In_Atoms.
Qed.

Lemma in_ngamma_del_ai_rev work ds ni i bs ai a c :
  invariant ai ->
  lookup ai i = Some bs ->
  in_ngamma work ds ni ai a c ->
  in_ngamma work ds ni (delete i ai) a c +
    {exists b n, onth bs n = Some b /\ c = AImp i b}.
Proof.
move=>Ha L; case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- move=>j b n bs0 H1 H2; case: (eqVneq j i)=>[E|N].
  - rewrite {j}E in H1 *; right; exists b, n; split=>//.
    by move: L; rewrite H1; case=><-.
  left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs0)=>//.
  by rewrite lookup_delete //= (negbTE N).
by move=>k H; left; apply: In_Atoms.
Qed.

Lemma in_ngamma_ins_a_tail work ds ni ai i a c :
  invariant a ->
  in_ngamma work ds ni ai a c ->
  in_ngamma work ds ni ai (upsert i (fun=>tt) tt a) c.
Proof.
move=>Ha; case=>{c}.
- by move=>n c; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>j b n bs H1 H2; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
move=>j H; apply: In_Atoms.
rewrite lookup_upsert //=; case: eqP=>// <-.
by case/optP: H; case=>->.
Qed.

Lemma in_ngamma_ins_a_head work ds ni ai i a :
  invariant a ->
  in_ngamma work ds ni ai (upsert i (fun=>tt) tt a) (NAtom i).
Proof.
move=>Ha; apply: In_Atoms.
rewrite lookup_upsert //= eqxx.
by case: (lookup a i).
Qed.

Lemma in_ngamma_ins_a_rev work ds ni ai i a c :
  invariant a ->
  in_ngamma work ds ni ai (upsert i (fun=>tt) tt a) c ->
  in_ngamma work ds ni ai a c + {c = NAtom i}.
Proof.
move=>Ha; case=>{c}.
- by move=>n c; left; apply: (In_Work _ _ _ _ _ n).
- by move=>n j k H; left; apply: (In_Disjs _ _ _ _ _ n).
- by move=>n x H; left; apply: (In_Nested_Imps _ _ _ _ _ n).
- by move=>j b n bs H1 H2; left; apply: (In_Atomic_Imps _ _ _ _ _ _ _ n bs).
move=>j H; case: (eqVneq j i)=>[->|N]; first by right.
move: H; rewrite lookup_upsert //= (negbTE N) => H.
by left; apply: In_Atoms.
Qed.

(********************************************************************)

Lemma in_ngamma_shift_work_ds i j work ds ni ai a c :
  in_ngamma (NDisj i j :: work) ds ni ai a c ->
  in_ngamma work ((i, j) :: ds) ni ai a c.
Proof.
case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_cons_ds_tail.
by exact: in_ngamma_cons_ds_head.
Qed.

Lemma in_ngamma_shift_ds_work i j work ds ni ai a c :
  in_ngamma work ((i, j) :: ds) ni ai a c ->
  in_ngamma (NDisj i j :: work) ds ni ai a c.
Proof.
case/in_ngamma_cons_ds_rev=>[H|->].
- by apply: in_ngamma_cons_work_tail.
by exact: in_ngamma_cons_work_head.
Qed.

Lemma in_ngamma_shift_work_ni x work ds ni ai a c :
  in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a c ->
  in_ngamma work ds (x :: ni) ai a c.
Proof.
case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_cons_ni_tail.
by exact: in_ngamma_cons_ni_head.
Qed.

Lemma in_ngamma_shift_ni_work x work ds ni ai a c :
  in_ngamma work ds (x :: ni) ai a c ->
  in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds ni ai a c.
Proof.
case/in_ngamma_cons_ni_rev=>[H|->].
- by apply: in_ngamma_cons_work_tail.
by exact: in_ngamma_cons_work_head.
Qed.

Lemma in_ngamma_shift_work_ni_x_ni x work ds ni1 ni2 ai a c :
  in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a c ->
  in_ngamma work ds (ni1 ++ x :: ni2) ai a c.
Proof.
case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_ni_x_ni_tail.
by exact: in_ngamma_ni_x_ni_head.
Qed.

Lemma in_ngamma_shift_ni_x_ni_work x work ds ni1 ni2 ai a c :
  in_ngamma work ds (ni1 ++ x :: ni2) ai a c ->
  in_ngamma (NImp_NF (nested_imp2nimp x) :: work) ds (ni1 ++ ni2) ai a c.
Proof.
case/in_ngamma_ni_x_ni_rev=>[H|->].
- by apply: in_ngamma_cons_work_tail.
by exact: in_ngamma_cons_work_head.
Qed.

Lemma in_ngamma_shift_work_ai_new work ds ni i b ai a c :
  invariant ai -> ~~ lookup ai i ->
  in_ngamma (AImp i b :: work) ds ni ai a c ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a c.
Proof.
move=>Ha Hl; case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_ins_ai_tail.
by apply: in_ngamma_ins_ai_head_new.
Qed.

Lemma in_ngamma_shift_work_ai_old work ds ni i b bs ai a c :
  invariant ai -> lookup ai i = Some bs ->
  in_ngamma (AImp i b :: work) ds ni ai a c ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a c.
Proof.
move=>Ha Hl; case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_ins_ai_tail.
by apply (in_ngamma_ins_ai_head_old _ _ _ _ _ bs).
Qed.

Lemma in_ngamma_shift_ai_work work ds ni i b ai a c :
  invariant ai ->
  in_ngamma work ds ni (upsert i (cons b) [::b] ai) a c ->
  in_ngamma (AImp i b :: work) ds ni ai a c.
Proof.
move=>Ha; case/in_ngamma_ins_ai_rev=>// [H|->].
- by apply: in_ngamma_cons_work_tail.
by exact: in_ngamma_cons_work_head.
Qed.

Lemma in_ngamma_shift_work_a work ds ni ai i a c :
  invariant a ->
  in_ngamma (NAtom i :: work) ds ni ai a c ->
  in_ngamma work ds ni ai (upsert i (fun=>tt) tt a) c.
Proof.
move=>Ha; case/in_ngamma_cons_work_rev=>[H|->].
- by apply: in_ngamma_ins_a_tail.
by apply: in_ngamma_ins_a_head.
Qed.

Lemma in_ngamma_shift_a_work work ds ni ai i a c :
  invariant a ->
  in_ngamma work ds ni ai (upsert i (fun=>tt) tt a) c ->
  in_ngamma (NAtom i :: work) ds ni ai a c.
Proof.
move=>Ha; case/in_ngamma_ins_a_rev=>// [H|->].
- by apply: in_ngamma_cons_work_tail.
by exact: in_ngamma_cons_work_head.
Qed.

End In_NGamma.

Arguments Undecorated [disp A].
Arguments Decorated [disp A].
