From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat seq bigop order.
From ipcssr Require Import prelude.
Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Inductive form A : Type :=
  | Falsum : form A
  | Atom : A -> form A
  | AndF : form A -> form A -> form A
  | OrF : form A -> form A -> form A
  | Imp : form A -> form A -> form A.

Arguments Falsum {A}.
Arguments Atom [A].
Arguments AndF [A].
Arguments OrF [A].
Arguments Imp [A].

Section Form.
Context {A : Type}.

Fixpoint vimp (qs : seq A) (f : form A) : form A :=
  if qs is q::qs' then vimp qs' (Imp (Atom q) f) else f.

End Form.

Section FormEq.
Context {A : eqType}.

Fixpoint eqform (f1 f2 : form A) :=
  match f1, f2 with
  | Falsum    , Falsum     => true
  | Atom i1   , Atom i2    => i1 == i2
  | AndF l1 r1, AndF l2 r2 => eqform l1 l2 && eqform r1 r2
  | OrF l1 r1 , OrF l2 r2  => eqform l1 l2 && eqform r1 r2
  | Imp l1 r1 , Imp l2 r2  => eqform l1 l2 && eqform r1 r2
  | _         , _          => false
  end.

Lemma eqformP: Equality.axiom eqform.
Proof.
elim=>[|i1|l1 IHl r1 IHr|l1 IHl r1 IHr|l1 IHl r1 IHr]; case=>[|i2|l2 r2|l2 r2|l2 r2] /=; try by constructor.
- case: (eqVneq i1 i2)=>[->|N]; constructor=>//.
  by apply: contra_neq_not N; case.
- by apply: (equivP (andPP (IHl l2) (IHr r2))); split; [case=>->-> | case].
- by apply: (equivP (andPP (IHl l2) (IHr r2))); split; [case=>->-> | case].
by apply: (equivP (andPP (IHl l2) (IHr r2))); split; [case=>->-> | case].
Qed.

Canonical form_eqMixin := EqMixin eqformP.
Canonical form_eqType := Eval hnf in EqType (form A) form_eqMixin.

Fixpoint subst_form (i : A) (a b : form A) : form A :=
  match b with
  | Falsum     => Falsum
  | Atom j     => if i == j then a else Atom j
  | AndF b0 b1 => AndF (subst_form i a b0) (subst_form i a b1)
  | OrF  b0 b1 => OrF  (subst_form i a b0) (subst_form i a b1)
  | Imp  b0 b1 => Imp  (subst_form i a b0) (subst_form i a b1)
  end.

Definition subst_list (i : A) (a : form A) (l : seq (form A)) :=
  map (subst_form i a) l.

(* TODO onth? direction? *)
Lemma subst_nth (i : A) (g : form A) (n : nat) (l : seq (form A)) (z : form A) :
  subst_form i g (nth z l n) = nth (subst_form i g z) (subst_list i g l) n.
Proof.
elim: l n=>[|h l IH]/= n; first by rewrite !nth_nil.
by case: n.
Qed.

End FormEq.

Section FormOrd.
Context {disp : unit} {A : orderType disp}.

Fixpoint below_form (a : form A) (i : A) {struct a} : bool :=
  match a with
  | Falsum => true
  | Atom j => (j < i)%O
  | AndF x y => below_form x i && below_form y i
  | OrF  x y => below_form x i && below_form y i
  | Imp  x y => below_form x i && below_form y i
  end.

Definition below_list (l : seq (form A)) (i : A) :=
  all (below_form^~ i) l.

Lemma less_below_form_imply (a : form A) (i j : A) :
  (i < j)%O -> below_form a i ==> below_form a j.
Proof.
move=>H; elim: a=>//=.
- by move=>a; apply/implyP=>Ha; apply/lt_trans/H.
- by move=>f hf g Hg; apply: implyb_tensor.
- by move=>f hf g Hg; apply: implyb_tensor.
by move=>f hf g Hg; apply: implyb_tensor.
Qed.

Lemma less_below_list_imply (l : seq (form A)) (i j : A) :
  (i < j)%O -> below_list l i ==> below_list l j.
Proof.
move=>H; rewrite /below_list.
by apply/implyP/sub_all=>a; apply/implyP/less_below_form_imply.
Qed.

Lemma subst_form_below (i : A) (g a : form A) :
  below_form a i -> subst_form i g a = a.
Proof.
elim: a=>//=.
- by move=>a; rewrite lt_neqAle eq_sym=>/andP [/negbTE->].
- by move=>k IHk l IHl /andP [/IHk->/IHl->].
- by move=>k IHk l IHl /andP [/IHk->/IHl->].
by move=>k IHk l IHl /andP [/IHk->/IHl->].
Qed.

Lemma subst_list_below (i : A) (g : form A) (l : seq (form A)) :
  below_list l i -> subst_list i g l = l.
Proof.
rewrite /below_list /subst_list; elim: l=>//= h l IH.
case/andP=>H /IH->.
by rewrite (subst_form_below _ _ _ H).
Qed.

Lemma below_vimp (i : A) (l : seq A) (a b : form A) :
  (forall j : A, below_form a j ==> below_form b j) ->
  below_form (vimp l a) i ==> below_form (vimp l b) i.
Proof.
elim: l =>//= k l IH in a b *; move=>H.
by apply: IH=>/= j; apply/implyb_tensor.
Qed.

Lemma below_vimp_head (i : A) (l : seq A) (a : form A) :
  below_form (vimp l a) i ==> below_form a i.
Proof.
elim: l a=>//= h l IH a.
apply/implyb_trans/IH/below_vimp=>/= j.
by apply/implyP; case/andP.
Qed.

Lemma below_vimp_split (j : A) (l : seq A) (a : form A) :
  {in l, forall i, (i < j)%O} ->
  below_form a j ==> below_form (vimp l a) j.
Proof.
elim: l a=>//= h l IH a H.
apply/implyb_trans/IH=>/=; last first.
- by move=>z Hz; apply: (H z); rewrite inE Hz orbT.
apply/implyP=>->; rewrite andbT.
by apply: H; rewrite inE eqxx.
Qed.

Lemma below_vimp_tail (j : A) (l : seq A) (a : form A) :
  below_form (vimp l a) j -> {in l, forall i, (i < j)%O}.
Proof.
elim: l a=>//= h l IH a H z.
rewrite inE; case/orP=>[/eqP{z}->|]; last by apply: (IH _ H).
move: (below_vimp_head j l (Imp (Atom h) a))=>/=.
by move/implyP=>/(_ H); case/andP.
Qed.

Lemma subst_vimp_head (j : A) (l : seq A) (a b : form A) :
  {in l, forall i, (i < j)%O} ->
  subst_form j a (vimp l b) = vimp l (subst_form j a b).
Proof.
elim: l=>//= h l IH in a b *; move=>H.
rewrite IH /=; last first.
- by move=>z Hz; apply: (H z); rewrite inE Hz orbT.
case: eqP=>// E.
by move: (H j); rewrite E inE eqxx ltxx /= => /(_ erefl).
Qed.

End FormOrd.

(* could be abstracted as ssr num but probably not worth it *)
Section FormNat.

Fixpoint max_int_of_form (f : form nat) : nat :=
  match f with
  | Falsum => 0
  | Atom i => i.+1
  | AndF f0 f1 => maxn (max_int_of_form f0) (max_int_of_form f1)
  | OrF  f0 f1 => maxn (max_int_of_form f0) (max_int_of_form f1)
  | Imp  f0 f1 => maxn (max_int_of_form f0) (max_int_of_form f1)
  end.

Lemma max_int_of_form_below (a : form nat) : below_form a (max_int_of_form a).
Proof.
elim: a=>//=.
- by move=>a; rewrite ltEnat /= ltnS.
- move=>f IHf g IHg.
  case: (ltngtP (max_int_of_form f) (max_int_of_form g))=>H.
  - by rewrite IHg andbT; move: IHf; apply/implyP/less_below_form_imply.
  - by rewrite IHf; move: IHg; apply/implyP/less_below_form_imply.
  by rewrite IHf /= H.
- move=>f IHf g IHg.
  case: (ltngtP (max_int_of_form f) (max_int_of_form g))=>H.
  - by rewrite IHg andbT; move: IHf; apply/implyP/less_below_form_imply.
  - by rewrite IHf; move: IHg; apply/implyP/less_below_form_imply.
  by rewrite IHf /= H.
move=>f IHf g IHg.
case: (ltngtP (max_int_of_form f) (max_int_of_form g))=>H.
- by rewrite IHg andbT; move: IHf; apply/implyP/less_below_form_imply.
- by rewrite IHf; move: IHg; apply/implyP/less_below_form_imply.
by rewrite IHf /= H.
Qed.

Definition max_int_of_list (l : seq (form nat)) : nat :=
  foldr (fun s => maxn (max_int_of_form s)) 0 l.

Lemma max_int_of_list_below (g : seq (form nat)) : below_list g (max_int_of_list g).
Proof.
elim: g=>//=h g IH.
have H := max_int_of_form_below h.
case: (ltngtP (max_int_of_form h) (max_int_of_list g))=>H2.
- by rewrite IH andbT; move: H; apply/implyP/less_below_form_imply.
- by rewrite H /=; move: IH; apply/implyP/less_below_list_imply.
by rewrite H /= H2.
Qed.

End FormNat.
