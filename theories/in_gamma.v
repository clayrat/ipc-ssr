From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq.
From ipcssr Require Import prelude forms normal_forms.

Variant in_gamma {A} (gamma : seq (form A)) (work : seq (normal_form A)) : form A -> Type :=
  | In_Gamma n a : onth gamma n = Some a -> in_gamma gamma work a
  | In_Work1 n a : onth work n = Some a -> in_gamma gamma work (nf2form a).

Section In_NGamma.
Context {A : Type}.

Lemma in_gamma_cons_gamma_tail (a : form A) gamma work c :
  in_gamma gamma work c -> in_gamma (a :: gamma) work c.
Proof. by case=>n b H; [apply: (In_Gamma _ _ n.+1) | apply: (In_Work1 _ _ n)]. Qed.

Lemma in_gamma_cons_gamma_head (a : form A) gamma work :
  in_gamma (a :: gamma) work a.
Proof. by apply: (In_Gamma _ _ 0). Qed.

Lemma in_gamma_cons_gamma_rev (a : form A) gamma work c :
  in_gamma (a :: gamma) work c -> in_gamma gamma work c + {c = a}.
Proof.
case.
- case=>[|n] b /=; first by case=>->; right.
  by move=>H; left; apply: (In_Gamma _ _ n).
by move=>n b H; left; apply/In_Work1/H.
Qed.

Lemma in_gamma_cons_work_tail (a : normal_form A) gamma work c :
  in_gamma gamma work c -> in_gamma gamma (a :: work) c.
Proof. by case=>n b H; [apply/In_Gamma/H | apply: (In_Work1 _ _ n.+1)]. Qed.

Lemma in_gamma_cons_work_head (a : normal_form A) gamma work :
  in_gamma gamma (a :: work) (nf2form a).
Proof. by apply: (In_Work1 _ _ 0). Qed.

Lemma in_gamma_cons_work_rev (a : normal_form A) gamma work c :
  in_gamma gamma (a :: work) c -> in_gamma gamma work c + {c = nf2form a}.
Proof.
case.
- by move=>n b H; left; apply/In_Gamma/H.
case=>[|n] b /=; first by case=>->; right.
by move=>H; left; apply: (In_Work1 _ _ n).
Qed.

(********************************************************************)

Lemma in_gamma_shift_gamma_work (a : normal_form A) gamma work c :
  in_gamma (nf2form a :: gamma) work c -> in_gamma gamma (a :: work) c.
Proof.
case/in_gamma_cons_gamma_rev=>[H|->].
- by apply: in_gamma_cons_work_tail.
by apply: in_gamma_cons_work_head.
Qed.

Lemma in_gamma_shift_work_gamma (a : normal_form A) gamma work c :
  in_gamma gamma (a :: work) c -> in_gamma (nf2form a :: gamma) work c.
Proof.
case/in_gamma_cons_work_rev=>[H|->].
- by apply/in_gamma_cons_gamma_tail.
by apply/in_gamma_cons_gamma_head.
Qed.

End In_NGamma.
