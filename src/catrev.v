From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq eqtype order.
From ipcssr Require Import kripke_trees normal_forms in_ngamma.

Section Catrev.
Context {disp : unit}.

Definition decorated_nested_imp (A : orderType disp) := (nimp A * kripke_tree A)%type.

Context {A : orderType disp}.

(* for efficiency, I guess? *)
Fixpoint catrev_d (ds : seq (decorated_nested_imp A)) (ni : seq (nested_imp A)) : seq (nested_imp A) :=
  match ds with
  | nil => ni
  | (x, k) :: ds => catrev_d ds (Decorated x k :: ni)
  end.

Lemma catrev_d_eq ds ni :
  catrev_d ds ni = catrev (map (fun '(x,k) => Decorated x k) ds) ni.
Proof. by elim: ds ni=>//= [[x k] ds] IH. Qed.

Corollary rev_app_app dni ni :
  catrev_d dni ni = catrev_d dni [::] ++ ni.
Proof. by rewrite !catrev_d_eq -catrev_catr. Qed.

Corollary in_ni_x_ni_rev (x x' : nested_imp A) (ni1 ni2 : seq (nested_imp A)) :
  x \in ni1 ++ x' :: ni2 -> x \in ni1 ++ ni2 \/ x = x'.
Proof.
by rewrite !mem_cat inE orbCA; case/orP=>[/eqP<-|->]; [right | left].
Qed.

Corollary in_ni_x_ni_tail (x x' : nested_imp A) (ni1 ni2 : seq (nested_imp A)) :
  x \in ni1 ++ ni2 -> x \in ni1 ++ x' :: ni2.
Proof.
by rewrite !mem_cat inE=>H; rewrite orbCA; apply/orP; right.
Qed.

(***********************************************************************)

Lemma rev_app_lemma0 (dni : seq (decorated_nested_imp A)) (ni : seq (nested_imp A)) :
  {dni_ni : seq (nested_imp A) | dni_ni = catrev_d dni ni}.
Proof.
elim: dni ni=>/= [|[x k] dni IH] ni; first by exists ni.
by apply: IH.
Qed.

Lemma rev_app_lemma2 {T : Type} (dni : seq (decorated_nested_imp A)) (ni : seq (nested_imp A)) :
  (forall dni_ni, dni_ni = catrev_d dni ni -> T) -> T.
Proof.
by case: (rev_app_lemma0 dni ni)=>x <-; apply.
Qed.

End Catrev.
