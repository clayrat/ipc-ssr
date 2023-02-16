From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq bigop choice.
From ipcssr Require Import prelude.

Inductive tree A := TNode of A & seq (tree A).
Arguments TNode [A].

Section Tree.
Context {A : Type}.

(* a leaf is a node with an empty list *)
Definition lf a : tree A := TNode a [::].

Lemma tree_ind' (P : tree A -> Prop) :
  (forall a l, all_prop P l -> P (TNode a l)) ->
  forall t, P t.
Proof.
move=> indu; fix H 1.
elim => a l; apply indu.
by elim: l.
Qed.

Lemma tree_rec' (P : tree A -> Type) :
  (forall a l, all_type P l -> P (TNode a l)) ->
  forall t, P t.
Proof.
move=>indu; fix H 1.
elim => a l; apply: indu.
by elim: l.
Qed.

(*
Fixpoint height (t : tree A) : nat :=
  let: TNode _ l := t in (\max_(i <- map height l) i).+1.
*)

Definition root (t : tree A) : A :=
  let: TNode w _ := t in w.

Definition children_of_node (t : tree A) : seq (tree A) :=
  let: TNode _ l := t in l.

End Tree.

Section EncodeDecodeTree.
Variable A : Type.

Fixpoint encode_tree (t : tree A) : GenTree.tree A :=
  match t with
  | TNode a [::] => GenTree.Leaf a
  | TNode a l => GenTree.Node O(*dummy*) (GenTree.Leaf a :: map encode_tree l)
  end.

Fixpoint decode_tree (t : GenTree.tree A) : option (tree A) :=
  match t with
  | GenTree.Leaf a => Some (TNode a [::])
  | GenTree.Node _ (GenTree.Leaf h :: l) => Some (TNode h (pmap decode_tree l))
  | GenTree.Node _ _ => None
  end.

Lemma pcancel_tree : pcancel encode_tree decode_tree.
Proof.
elim/(@tree_ind' A) => a [//|b s /= [-> H2 /=]]; congr (Some (TNode _ (_ :: _))).
elim: s H2 => // c s IH /= [-> K2 /=]; by rewrite IH.
Qed.

End EncodeDecodeTree.

Definition tree_eqMixin (A : eqType) := PcanEqMixin (@pcancel_tree A).
Canonical tree_eqType (A : eqType) := Eval hnf in EqType _ (@tree_eqMixin A).

(* we formulate the rest of the theory with decidable equality for convenience *)
(* this is because we only use it for Kripke trees whose elements are *)
(* sets (AVL-maps) of atoms, which implies dec. eq. *)
Section TreeEq.
Context {A : eqType}.

Fixpoint mem_tree (t : tree A) : pred A :=
  let: TNode x l := t in
  fun a => (a == x) || has (mem_tree^~ a) l.

Definition tree_eqclass := tree A.
Identity Coercion tree_of_eqclass : tree_eqclass >-> tree.
Coercion pred_of_tree (t : tree_eqclass) : {pred A} := mem_tree t.

Canonical tree_predType := PredType (pred_of_tree : tree A -> pred A).
(* The line below makes mem_tree a canonical instance of topred. *)
Canonical mem_tree_predType := PredType mem_tree.

Lemma in_tnode a t ts : (t \in TNode a ts) = (t == a) || has (fun q => t \in q) ts.
Proof. by []. Qed.

(* successor *)

Fixpoint successor (t1 t2 : tree A) : bool :=
  (t1 == t2) || has (successor t1) (children_of_node t2).

Lemma successor_refl : reflexive successor.
Proof. by case=>/= a ts; rewrite eqxx. Qed.

Lemma successor_trans : transitive successor.
Proof.
move=>t2 t1; elim/(@tree_ind' A)=>a3 ts3 /= IH H1.
case/orP=>[/eqP E2|]; first by rewrite E2 in H1.
case/hasP=>z Hz Pz; apply/orP; right; apply/hasP; exists z=>//.
by move: H1 Pz; apply: (all_prop_mem IH).
Qed.

Lemma successorP t1 t2 :
  reflect (t1 = t2 \/ exists2 t, t \in children_of_node t2 & successor t1 t)
          (successor t1 t2).
Proof.
apply: (iffP idP).
- by case: t2=>/=a2 ts2; case/orP=>[/eqP->|/hasP H]; [left | right].
case=>[->|[t Ht St]]; first by exact: successor_refl.
by case: t2 Ht=>/= a ts2 Ht; apply/orP; right; apply/hasP; exists t.
Qed.

(* never used? *)
Lemma successor_ind (P : tree A -> Prop) :
  (forall a, P (lf a)) ->
  (forall t0 t1, successor t0 t1 -> P t0 -> P t1) ->
  forall t, P t.
Proof.
move=>Pl Pc t.
apply: tree_ind'=>a [_ |h ts /= [Ph Pts]]; first by apply: Pl.
by apply: (Pc h)=>//=; rewrite successor_refl orbT.
Qed.

Lemma successor_subset (t t0 : tree A) :
  successor t t0 -> {subset t <= t0}.
Proof.
elim/(@tree_ind' A): t0=>a0 ts0 /= IH.
case/orP=>[/eqP->|] //; case/hasP=>/= z Hz Sz.
have H: {subset t <= z} by apply: (all_prop_mem IH).
move=>q /H Hq; rewrite in_tnode /=.
by apply/orP; right; apply/hasP; exists z.
Qed.

(* monotone *)

Context {I : Type}.

Fixpoint Is_Monotone_Tree (P : A -> I -> bool) (t : tree A) : Prop :=
  let: TNode x l := t in
  all_prop (fun t => (forall i, P x i ==> P (root t) i)
                  /\ Is_Monotone_Tree P t) l.

Lemma successor_is_monotone_tree {P} (t t0 : tree A) :
  successor t0 t -> Is_Monotone_Tree P t -> Is_Monotone_Tree P t0.
Proof.
elim/(@tree_ind' A): t=>a ts /= IH.
case/orP=>[/eqP->|] //; case/hasP=>/= z Hz Sz H.
apply: (all_prop_mem IH z) =>{t0 Sz IH}//.
by case: (all_prop_mem H _ Hz).
Qed.

Definition Is_Monotone (P : A -> I -> bool) (t : tree A) : Prop :=
  forall t0 t1 : tree A,
  successor t1 t0 -> successor t0 t ->
  forall i : I, P (root t0) i ==> P (root t1) i.

Lemma successor_is_monotone {P} (t t0 : tree A) :
  successor t0 t -> Is_Monotone P t -> Is_Monotone P t0.
Proof.
move=>S0; rewrite /Is_Monotone => H t1 t2 S21 S10.
by apply: H=>//; apply/successor_trans/S0.
Qed.

Lemma is_monotone_tree_is_monotone {P} t :
  Is_Monotone_Tree P t -> Is_Monotone P t.
Proof.
rewrite /Is_Monotone=>H t0 t1 S10 S0 i.
move: (successor_is_monotone_tree _ _ S0 H)=>{S0 H}.
elim/(@tree_ind' A): t0 S10=>a0 ts0 /= IH.
case/orP=>[/eqP-> _|] //=; case/hasP=>/= z Hz Sz H.
case: (all_prop_mem H _ Hz)=>Hi Hmz.
apply: (implyb_trans (y:=P (root z) i))=>//.
by apply: (all_prop_mem IH).
Qed.

End TreeEq.
