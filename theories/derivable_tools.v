From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat eqtype seq order.
From ipcssr Require Import prelude forms derivations derivable_def.

Section Derivable.
Context {A : Type}.

Lemma derivable_weak ctx (a b : form A) :
  Derivable ctx a -> Derivable (b :: ctx) a.
Proof.
case=>t Dt; apply: (Derivable_Intro _ _ (Shift t)).
by apply: ShiftIntro.
Qed.

Lemma derivable_weak_list ctx1 ctx2 (a : form A) :
  Derivable ctx1 a -> Derivable (ctx2 ++ ctx1) a.
Proof. by elim: ctx2=>//= b ctx2 /[apply]; apply: derivable_weak. Qed.

Lemma derivable_cut_aux ctx t (b : form A) :
  derives ctx t b ->
  forall a l1 l2,
  ctx = l1 ++ a :: l2 -> Derivable [::] a -> Derivable (l1 ++ l2) b.
Proof.
elim/(@derives_rec A)=>{ctx t b}.
- move=>g n a + b l1 l2 E; rewrite {g}E onth_cat /=.
  case: (ltngtP n (size l1))=>Hn.
  - move=>H _; apply/(Derivable_Intro _ _ (Var n))/ByAssumption.
    by rewrite onth_cat Hn.
  - move=>Ha Db; apply/(Derivable_Intro _ _ (Var n.-1))/ByAssumption.
    rewrite onth_cat ltnNge.
    move: (Hn); rewrite -{1}(ltn_predK Hn) ltnS=>->/=.
    rewrite -predn_sub; case Ek: (n - size l1) Ha=>[|k] //.
    by move: Hn; rewrite -subn_gt0 Ek.
  rewrite Hn subnn; case=>{b}-> D.
  by rewrite -(cats0 (l1++l2)); apply: derivable_weak_list.
- move=>g _ a _ IH b l1 l2 /IH/[apply]; case=>t Df.
  by apply/(Derivable_Intro _ _ (Efq t a))/ByAbsurdity.
- move=>g a _ b _ IH c l1 l2 E Dc.
  case: (IH c (a::l1) l2)=>//= [|t Db]; first by rewrite E.
  by apply/(Derivable_Intro _ _ (Abs a t))/ImpIntro.
- move=>g _ _ a b _ IHab _ IHa c l1 l2 E Dc.
  case: (IHab _ _ _ E Dc)=>r Dab.
  case: (IHa _ _ _ E Dc)=>s Da.
  by apply/(Derivable_Intro _ _ (App a r s))/ImpElim.
- move=>g _ _ a b _ IHa _ IHb c l1 l2 E Dc.
  case: (IHa _ _ _ E Dc)=>r Da.
  case: (IHb _ _ _ E Dc)=>s Db.
  by apply/(Derivable_Intro _ _ (Pair r s))/AndFIntro.
- move=>g _ a b _ IH c l1 l2 E Dc.
  case: (IH _ _ _ E Dc)=>t Dab.
  by apply/(Derivable_Intro _ _ (PrL b t))/AndFElimL.
- move=>g _ a b _ IH c l1 l2 E Dc.
  case: (IH _ _ _ E Dc)=>t Dab.
  by apply/(Derivable_Intro _ _ (PrR a t))/AndFElimR.
- move=>g _ a b _ IH c l1 l2 E Dc.
  case: (IH _ _ _ E Dc)=>t Da.
  by apply/(Derivable_Intro _ _ (OrFL t b))/OrFIntroL.
- move=>g _ a b _ IH c l1 l2 E Dc.
  case: (IH _ _ _ E Dc)=>t Da.
  by apply/(Derivable_Intro _ _ (OrFR t a))/OrFIntroR.
- move=>g _ _ _ a b c _ IHab _ IHa _ IHb  d l1 l2 E Dd.
  case: (IHab _ _ _ E Dd)=>r Dab.
  case: (IHa d (a::l1) l2)=>//= [|s Da]; first by rewrite E.
  case: (IHb d (b::l1) l2)=>//= [|t Db]; first by rewrite E.
  by apply/(Derivable_Intro _ _ (Cas a b r s t))/OrFElim.
move=>g r a b Dr IH c l1 l2 E Dc.
case: l1 E=>/= [|a' l1]; case.
- by move=>_ <-; apply/Derivable_Intro/Dr.
move=><- E; case: (IH _ _ _ E Dc)=>t Dt.
by apply/derivable_weak/Derivable_Intro/Dt.
Qed.

Lemma derivable_cut ctx (a b : form A) :
  Derivable [::] a -> Derivable (a :: ctx) b -> Derivable ctx b.
Proof.
move=>Da; case=>t Db; rewrite -(cat0s ctx).
by apply/(derivable_cut_aux _ _ _ Db)/Da.
Qed.

Lemma derivable_cut_merge ctx (a b : form A) :
  Derivable ctx a -> Derivable (a :: ctx) b -> Derivable ctx b.
Proof.
elim: ctx=>[|c ctx IH] in a b *.
- by apply: derivable_cut.
move=>Da Db.
case: (IH (Imp c a) (Imp c b)).
- by case: Da=>t Dt; apply/(Derivable_Intro _ _ (Abs c t))/ImpIntro.
- case: Db=>t Dt.
  apply: (Derivable_Intro _ _ (Abs c (App a (App c (Shift (Shift (Abs c (Abs a t)))) (Var 0))
                                            (App c (Var 1) (Var 0))))).
  apply/ImpIntro/ImpElim.
  - apply/ImpElim; last by apply: ByAssumption.
    by apply/ShiftIntro/ShiftIntro/ImpIntro/ImpIntro.
  by apply/ImpElim; apply: ByAssumption.
move=>t Dt; apply (Derivable_Intro _ _(App c (Shift t) (Var 0))).
apply/ImpElim; last by apply: ByAssumption.
by apply/ShiftIntro.
Qed.

(************************************************************************)

Lemma derivable_a_imp_a (a : form A) : Derivable [::] (Imp a a).
Proof.
by apply/(Derivable_Intro _ _ (Abs a (Var 0)))/ImpIntro/ByAssumption.
Qed.

Lemma derivable_a_and_b__derivable_a ctx (a b : form A) :
  Derivable ctx (AndF a b) -> Derivable ctx a.
Proof. by case=>t Dt; apply/(Derivable_Intro _ _ (PrL b t))/AndFElimL. Qed.

Lemma derivable_a_and_b__derivable_b ctx (a b : form A) :
  Derivable ctx (AndF a b) -> Derivable ctx b.
Proof. by case=>t Dt; apply/(Derivable_Intro _ _ (PrR a t))/AndFElimR. Qed.

Lemma derivable_falsum_or_a__derivable_a ctx (a : form A) :
  Derivable ctx (OrF Falsum a) -> Derivable ctx a.
Proof.
case=>t Dt.
apply/(Derivable_Intro _ _ (Cas Falsum a t (Efq (Var 0) a) (Var 0)))/OrFElim=>//.
- by apply/ByAbsurdity/ByAssumption.
by apply/ByAssumption.
Qed.

Lemma derivable_a_or_falsum__derivable_a ctx (a : form A) :
  Derivable ctx (OrF a Falsum) -> Derivable ctx a.
Proof.
case=>t Dt.
apply/(Derivable_Intro _ _ (Cas a Falsum t (Var 0) (Efq (Var 0) a)))/OrFElim=>//.
- by apply/ByAssumption.
by apply/ByAbsurdity/ByAssumption.
Qed.

Lemma derivable_a_imp_falsum_or_b__derivable_a_imp_b ctx (a b : form A) :
  Derivable ctx (Imp a (OrF Falsum b)) -> Derivable ctx (Imp a b).
Proof.
case=>t Dt.
apply/(Derivable_Intro _ _ (Abs a (Cas Falsum b (App a (Shift t) (Var 0)) (Efq (Var 0) b) (Var 0))))/ImpIntro/OrFElim.
- by apply: ImpElim; [apply: ShiftIntro | apply: ByAssumption].
- by apply/ByAbsurdity/ByAssumption.
by apply: ByAssumption.
Qed.

Lemma derivable_a_imp_b_or_falsum__derivable_a_imp_b ctx (a b : form A) :
  Derivable ctx (Imp a (OrF b Falsum)) -> Derivable ctx (Imp a b).
Proof.
case=>t Dt.
apply/(Derivable_Intro _ _ (Abs a (Cas b Falsum (App a (Shift t) (Var 0)) (Var 0) (Efq (Var 0) b))))/ImpIntro/OrFElim.
- by apply: ImpElim; [apply: ShiftIntro | apply: ByAssumption].
- by apply: ByAssumption.
by apply/ByAbsurdity/ByAssumption.
Qed.

Lemma derivable_a_and_b_imp_c__derivable_a_imp_b_imp_c ctx (a b c : form A) :
  Derivable ctx (Imp (AndF a b) c) -> Derivable ctx (Imp a (Imp b c)).
Proof.
case=>t Dt.
apply: (Derivable_Intro _ _ (Abs a (Abs b (App (AndF a b) (Shift (Shift t)) (Pair (Var 1) (Var 0)))))).
apply/ImpIntro/ImpIntro/ImpElim.
- by apply/ShiftIntro/ShiftIntro.
by apply: AndFIntro; apply: ByAssumption.
Qed.

Lemma derivable_a_or_b_imp_c__derivable_a_imp_c ctx (a b c : form A) :
  Derivable ctx (Imp (OrF a b) c) -> Derivable ctx (Imp a c).
Proof.
case=>t Dt.
apply: (Derivable_Intro _ _ (Abs a (App (OrF a b) (Shift t) (OrFL (Var 0) b)))).
apply/ImpIntro/ImpElim.
- by apply: ShiftIntro.
by apply/OrFIntroL/ByAssumption.
Qed.

Lemma derivable_a_or_b_imp_c__derivable_b_imp_c ctx (a b c : form A) :
  Derivable ctx (Imp (OrF a b) c) -> Derivable ctx (Imp b c).
Proof.
case=>t Dt.
apply: (Derivable_Intro _ _(Abs b (App (OrF a b) (Shift t) (OrFR (Var 0) a)))).
apply/ImpIntro/ImpElim.
- by apply: ShiftIntro.
by apply/OrFIntroR/ByAssumption.
Qed.

Lemma derivable_falsum_imp_b_imp_c__derivable_c ctx (b c : form A) :
  Derivable ctx (Imp (Imp Falsum b) c) -> Derivable ctx c.
Proof.
case=>t Dt.
apply: (Derivable_Intro _ _ (App (Imp Falsum b) t (Abs Falsum (Efq (Var 0) b)))).
apply: ImpElim=>//.
by apply/ImpIntro/ByAbsurdity/ByAssumption.
Qed.

Lemma derivable_b__derivable_a_imp_b ctx (a b : form A) :
  Derivable ctx b -> Derivable ctx (Imp a b).
Proof.
case=>t Dt.
by apply/(Derivable_Intro _ _ (Abs a (Shift t)))/ImpIntro/ShiftIntro.
Qed.

Lemma derivable_a_a_imp_b__derivable_b ctx (a b : form A) :
  Derivable ctx a -> Derivable ctx (Imp a b) -> Derivable ctx b.
Proof.
case=>t Dt; case=>s Ds.
by apply/(Derivable_Intro _ _  (App a s t))/ImpElim.
Qed.

Lemma derivable_a_context_b__derivable_a_imp_b ctx (a b : form A) :
  Derivable (a :: ctx) b -> Derivable ctx (Imp a b).
Proof.
case=>t Dt.
by apply/(Derivable_Intro _ _ (Abs a t))/ImpIntro.
Qed.

Lemma derivable_vimp ctx l (a b : form A) :
  (forall ctx, Derivable ctx a -> Derivable ctx b) ->
  Derivable ctx (vimp l a) -> Derivable ctx (vimp l b).
Proof.
elim: l=>[|c l IH] /= in a b *; move=>H.
- by apply: H.
apply: IH=>{}ctx.
case=>t Dt; case: (H (Atom c::ctx)).
- apply: (Derivable_Intro _ _ (App (Atom c) (Shift t) (Var 0))).
  by apply/ImpElim; [apply: ShiftIntro | apply: ByAssumption].
move=>s Ds; apply: (Derivable_Intro _ _ (Abs (Atom c) s)).
by apply: ImpIntro.
Qed.

Lemma derivable_vimp2 ctx l (a b c : form A) :
  (forall ctx,
   Derivable ctx a -> Derivable ctx b -> Derivable ctx c) ->
  Derivable ctx (vimp l a) -> Derivable ctx (vimp l b) ->
  Derivable ctx (vimp l c).
Proof.
elim: l=>[|d l IH] /= in a b c *; move=> H.
- by apply: H.
apply: IH=>{}ctx.
case=>t Dt; case=>s Ds.
case: (H (Atom d::ctx)).
- apply: (Derivable_Intro _ _ (App (Atom d) (Shift t) (Var 0))).
  by apply/ImpElim; [apply: ShiftIntro | apply: ByAssumption].
- apply: (Derivable_Intro _ _ (App (Atom d) (Shift s) (Var 0))).
  by apply/ImpElim; [apply: ShiftIntro | apply: ByAssumption].
move=>q Dq; apply: (Derivable_Intro _ _ (Abs (Atom d) q)).
by apply: ImpIntro.
Qed.

Lemma derivable_vimp0 ctx l (a : form A) :
  (forall ctx, Derivable ctx a) ->
  Derivable ctx (vimp l a).
Proof.
elim: l=>[|b l IH] /= in a *; move=>H.
- by apply: H.
apply: IH=>{}ctx.
case: (H (Atom b::ctx))=>t Dt.
apply: (Derivable_Intro _ _ (Abs (Atom b) t)).
by apply: ImpIntro.
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
