From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq order.
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

(* TODO *)
End Catrev.
