From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq order.
From ipcssr Require Import prelude forms derivations derivable_def.

Section Derivable.
Context {A : Type}.

Lemma derivable_weak ctx (a b : form A) :
 Derivable ctx a -> Derivable (b :: ctx) a.
Proof.
case=>t Dt; apply: (Derivable_Intro _ _ (Shift t)).
by apply: ShiftIntro.
Qed.

End Derivable.

Section DerivableEq.
Context {A : eqType}.

Lemma derivable_subst (i : A) g ctx a :
  Derivable ctx a ->
  Derivable (subst_list i g ctx) (subst_form i g a).
Proof.
case=>t; elim/(@derives_rec A)=>{a t ctx}.
- move=>ctx n a E.
  apply: (Derivable_Intro _ _ (Var n)).
  by apply: ByAssumption; rewrite subst_onth E.
- move=>ctx t a D [s /= D'].
  apply: (Derivable_Intro _ _ (Efq s (subst_form i g a))).
  by apply: ByAbsurdity.
- move=>ctx a r b D [t /= D'].
  apply: (Derivable_Intro _ _ (Abs (subst_form i g a) t)).
  by apply: ImpIntro.
- move=>ctx r s a b /= D1 [t Dt] D3 [q Dq].
  apply: (Derivable_Intro _ _ (App (subst_form i g a) t q)).
  by apply: ImpElim.
- move=>ctx r s a b /= Dr [t Dt] Ds [q Dq].
  apply: (Derivable_Intro _ _ (Pair t q)).
  by apply: AndFIntro.
- move=>ctx r a b /= Dr [t Dt].
  apply: (Derivable_Intro _ _ (PrL (subst_form i g b) t)).
  by apply: AndFElimL.
- move=>ctx r a b /= Dr [t Dt].
  apply: (Derivable_Intro _ _ (PrR (subst_form i g a) t)).
  by apply: AndFElimR.
- move=>ctx r a b /= Dr [t Dt].
  apply: (Derivable_Intro _ _ (OrFL t (subst_form i g b))).
  by apply: OrFIntroL.
- move=>ctx r a b /= Dr [t Dt].
  apply: (Derivable_Intro _ _ (OrFR t (subst_form i g a))).
  by apply: OrFIntroR.
- move=>ctx r s t a b c /= Dr [x Dx] Ds [y Dy] Dt [z Dz].
  apply: (Derivable_Intro _ _ (Cas (subst_form i g a) (subst_form i g b) x y z)).
  by apply: OrFElim.
move=>ctx r a b /= Dr [t Dt].
apply: (Derivable_Intro _ _ (Shift t)).
by apply: ShiftIntro.
Qed.

End DerivableEq.

Section DerivableOrd.
Context {disp : unit} {A : orderType disp}.

Lemma snd_order_inst ctx (i : A) :
  Derivable ctx (Atom i) ->
  below_list ctx i -> forall b, Derivable ctx b.
Proof.
move=>D B b.
have <-: subst_form i b (Atom i) = b by rewrite /= eqxx.
rewrite -(subst_list_below i b ctx) //.
by apply: derivable_subst.
Qed.

End DerivableOrd.


(*
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Extract Inductive reflect => bool [ true false ].

Extraction "ext.ml" derivable_subst.
*)