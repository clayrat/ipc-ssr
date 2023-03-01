From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq eqtype.
From ipcssr Require Import forms.

Inductive normal_form A : Type :=
  | NFalsum : normal_form A
  | NAtom : A -> normal_form A
  | NDisj : A -> A -> normal_form A
  | AImp : A -> normal_form A -> normal_form A
  | NImp_NF : nimp A -> normal_form A
with nimp A : Type :=
  | NImp : A -> A -> normal_form A -> nimp A.

Arguments NFalsum {A}.
Arguments NAtom [A].
Arguments NDisj [A].
Arguments AImp [A].
Arguments NImp_NF [A].
Arguments NImp [A].

Section NormalForms.
Context {A : Type}.

Fixpoint nf2form (nf : normal_form A) : form A :=
  match nf with
  | NFalsum => Falsum
  | NAtom i => Atom i
  | NDisj i j => OrF (Atom i) (Atom j)
  | AImp i b => Imp (Atom i) (nf2form b)
  | NImp_NF x => nimp2form x
  end

 with nimp2form (ni : nimp A) : form A :=
  let: NImp i j b := ni in
    Imp (Imp (Atom i) (Atom j)) (nf2form b).

Fixpoint nvimp (s : seq A) (a : normal_form A) : normal_form A :=
  if s is i :: l then nvimp l (AImp i a) else a.

Lemma vimp_eq_nvimp s a :
  vimp s (nf2form a) = nf2form (nvimp s a).
Proof.
elim: s=>//= h s IH in a *.
by rewrite -IH.
Qed.

End NormalForms.

Section NormalFormsEq.
Context {A : eqType}.

Fixpoint eqnf (nf1 nf2 : normal_form A) : bool :=
  match nf1, nf2 with
  | NFalsum    , NFalsum     => true
  | NAtom a1   , NAtom a2    => a1 == a2
  | NDisj a1 b1, NDisj a2 b2 => (a1 == a2) && (b1 == b2)
  | AImp a1 n1 , AImp a2 n2  => (a1 == a2) && eqnf n1 n2
  | NImp_NF n1 , NImp_NF n2  => eqnimp n1 n2
  | _          , _           => false
  end
with eqnimp (ni1 ni2 : nimp A) : bool :=
  let: NImp a1 b1 n1 := ni1 in
  let: NImp a2 b2 n2 := ni2 in
  [&& a1 == a2, b1 == b2 & eqnf n1 n2].

Fixpoint eqnfP (nf1 nf2 : normal_form A) : reflect (nf1 = nf2) (eqnf nf1 nf2)
with eqnimpP (ni1 ni2 : nimp A) : reflect (ni1 = ni2) (eqnimp ni1 ni2).
Proof.
- elim: nf1 nf2=>[|a1|a1 b1|a1 n1 IH|n1]; case=>[|a2|a2 b2|a2 n2|n2] /=; try by constructor.
  - by have [<-/=|Na] := a1 =P a2; constructor=>//; case.
  - have [<-|Na]/= := a1 =P a2; last by constructor; case.
    by have [<-|Nb]/= := b1 =P b2; constructor=>//; case.
  - have [<-|Na]/= := a1 =P a2; last by constructor; case.
    by apply: (iffP (IH n2))=>[->|[]].
  by apply: (iffP (eqnimpP n1 n2))=>[->|[]].
case: ni1=>a1 b1 n1; case: ni2=>a2 b2 n2 /=.
have [<-|Na] /= := a1 =P a2; last by constructor; case.
have [<-|Nb] /= := b1 =P b2; last by constructor; case.
by apply: (iffP (eqnfP n1 n2))=>[->|[]].
Qed.

Canonical normal_form_eqMixin := EqMixin eqnfP.
Canonical normal_form_eqType := Eval hnf in EqType (normal_form A) normal_form_eqMixin.
Canonical nimp_eqMixin := EqMixin eqnimpP.
Canonical nimp_eqType := Eval hnf in EqType (nimp A) nimp_eqMixin.

End NormalFormsEq.
