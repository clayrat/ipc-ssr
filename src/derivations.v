From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq.
From ipcssr Require Import prelude forms.

Inductive proof_term A : Type :=
  | Var   : nat -> proof_term A
  | Efq   : proof_term A -> form A -> proof_term A
  | Abs   : form A -> proof_term A -> proof_term A
  | App   : form A -> proof_term A -> proof_term A -> proof_term A
  | Pair  : proof_term A -> proof_term A -> proof_term A
  | PrL   : form A -> proof_term A -> proof_term A
  | PrR   : form A -> proof_term A -> proof_term A
  | OrFL  : proof_term A -> form A -> proof_term A
  | OrFR  : proof_term A -> form A -> proof_term A
  | Cas   : form A -> form A -> proof_term A -> proof_term A -> proof_term A -> proof_term A
  | Shift : proof_term A -> proof_term A.

Arguments Var [A].
Arguments Efq [A].
Arguments Abs [A].
Arguments App [A].
Arguments Pair [A].
Arguments PrL [A].
Arguments PrR [A].
Arguments OrFL [A].
Arguments OrFR [A].
Arguments Cas [A].
Arguments Shift [A].

Section Derivation.
Context {A : Type}.

Inductive derives : seq (form A) -> proof_term A -> form A -> Prop :=
| ByAssumption g n a    :
    onth g n = Some a -> derives g (Var n) a
| ByAbsurdity g t a     :
    derives g t Falsum -> derives g (Efq t a) a
| ImpIntro g a r b      :
    derives (a :: g) r b -> derives g (Abs a r) (Imp a b)
| ImpElim g r s a b     :
    derives g r (Imp a b) -> derives g s a -> derives g (App a r s) b
| AndFIntro g r s a b   :
    derives g r a -> derives g s b -> derives g (Pair r s) (AndF a b)
| AndFElimL g r a b     :
    derives g r (AndF a b) -> derives g (PrL b r) a
| AndFElimR g r a b     :
    derives g r (AndF a b) -> derives g (PrR a r) b
| OrFIntroL g r a b     :
    derives g r a -> derives g (OrFL r b) (OrF a b)
| OrFIntroR g r a b     :
    derives g r b -> derives g (OrFR r a) (OrF a b)
| OrFElim g r s t a b c :
    derives g r (OrF a b) -> derives (a :: g) s c -> derives (b :: g) t c -> derives g (Cas a b r s t) c
| ShiftIntro g r a b    :
    derives g r b -> derives (a :: g) (Shift r) b.

Lemma derives_rec (P : seq (form A) -> proof_term A -> form A -> Type) :
  (forall g n a,
     onth g n = Some a -> P g (Var n) a) ->
  (forall g t a,
     derives g t Falsum -> P g t Falsum -> P g (Efq t a) a) ->
  (forall g a r b,
     derives (a :: g) r b -> P (a :: g) r b -> P g (Abs a r) (Imp a b)) ->
  (forall g r s a b,
     derives g r (Imp a b) -> P g r (Imp a b) ->
     derives g s a -> P g s a -> P g (App a r s) b) ->
  (forall g r s a b,
     derives g r a -> P g r a ->
     derives g s b -> P g s b -> P g (Pair r s) (AndF a b)) ->
  (forall g r a b,
     derives g r (AndF a b) -> P g r (AndF a b) -> P g (PrL b r) a) ->
  (forall g r a b,
     derives g r (AndF a b) -> P g r (AndF a b) -> P g (PrR a r) b) ->
  (forall g r a b,
     derives g r a -> P g r a -> P g (OrFL r b) (OrF a b)) ->
  (forall g r a b,
     derives g r b -> P g r b -> P g (OrFR r a) (OrF a b)) ->
  (forall g r s t a b c,
     derives g r (OrF a b) -> P g r (OrF a b) ->
     derives (a :: g) s c -> P (a :: g) s c ->
     derives (b :: g) t c -> P (b :: g) t c -> P g (Cas a b r s t) c) ->
  (forall g r a b,
     derives g r b -> P g r b -> P (a :: g) (Shift r) b) ->
  forall g t a, derives g t a -> P g t a.
Proof.
move=>var efq abs app par prl prr orl orr cas shift /[swap]; elim.
- move=>n g a H; apply: var.
  by case: {-1}_ _ / H (erefl (@Var A n))=>// ???<-; case=>->.
- move=>t IH f g a H.
  have [-> Hd]: a = f /\ derives g t Falsum
    by case: {-1}_ _ / H (erefl (Efq t f))=>// ???? [-> ->].
  by apply: efq=>//; apply: IH.
- move=>f t IH g'; case.
  - move=>H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Abs f t)) (erefl (@Falsum A)).
  - move=>a H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Abs f t)) (erefl (Atom a)).
  - move=>f0 f1 H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Abs f t)) (erefl (AndF f0 f1)).
  - move=>f0 f1 H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Abs f t)) (erefl (OrF f0 f1)).
  move=>f0 f1 H.
  have [-> Hd]: f = f0 /\ derives (f0 :: g') t f1
    by case: _ {1}_ {1}_ / H (erefl (Abs f t)) (erefl (Imp f0 f1))=>// ????? [<-<-][<-<-].
  by apply: abs=>//; apply: IH.
- move=>f t IHt q IHq g a H.
  have [Hd1 Hd2]: derives g t (Imp f a) /\ derives g q f
    by case: _ {1}_ {1}_ / H (erefl (App f t q))=>// ??????? [<-<-<-].
  by apply: app=>//; [apply: IHt|apply: IHq].
- move=>l IHl r IHr g; case.
  - move=>H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Pair l r)) (erefl (@Falsum A)).
  - move=>a H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Pair l r)) (erefl (Atom a)).
  - move=>f0 f1 H.
    have [Hl Hr] : derives g l f0 /\ derives g r f1
      by case: _ {1}_ {1}_ / H (erefl (Pair l r)) (erefl (AndF f0 f1))=>// ??????? [<-<-][<-<-].
    by apply: par=>//; [apply: IHl|apply: IHr].
  - move=>f0 f1 H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (Pair l r)) (erefl (OrF f0 f1)).
  move=>f0 f1 H; exfalso.
  by case: {-1}_ {1}_ {1}_ / H (erefl (Pair l r)) (erefl (Imp f0 f1)).
- move=>b p IH g a H.
  have Hd: derives g p (AndF a b)
    by case: _ {1}_ {1}_ / H (erefl (PrL b p))=>// ????? [<-<-].
  by apply: prl =>//; apply: IH.
- move=>a p IH g b H.
  have Hd: derives g p (AndF a b)
    by case: _ {1}_ {1}_ / H (erefl (PrR a p))=>// ????? [<-<-].
  by apply: prr =>//; apply: IH.
- move=>p IH f g; case.
  - move=>H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFL p f)) (erefl (@Falsum A)).
  - move=>a H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFL p f)) (erefl (Atom a)).
  - move=>f0 f1 H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFL p f)) (erefl (AndF f0 f1)).
  - move=>f0 f1 H.
    have [-> Hd] : f = f1 /\ derives g p f0.
    - by case: _ {1}_ {1}_ / H (erefl (OrFL p f)) (erefl (OrF f0 f1))=>// ????? [<-<-][<-<-].
    by apply: orl=>//; apply: IH.
  move=>f0 f1 H; exfalso.
  by case: _ {1}_ {1}_ / H (erefl (OrFL p f)) (erefl (Imp f0 f1)).
- move=>p IH f g; case.
  - move=>H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFR p f)) (erefl (@Falsum A)).
  - move=>a H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFR p f)) (erefl (Atom a)).
  - move=>f0 f1 H; exfalso.
    by case: {-1}_ {1}_ {1}_ / H (erefl (OrFR p f)) (erefl (AndF f0 f1)).
  - move=>f0 f1 H.
    have [-> Hd] : f = f0 /\ derives g p f1.
    - by case: _ {1}_ {1}_ / H (erefl (OrFR p f)) (erefl (OrF f0 f1))=>// ????? [<-<-][<-<-].
    by apply: orr=>//; apply: IH.
  move=>f0 f1 H; exfalso.
  by case: _ {1}_ {1}_ / H (erefl (OrFR p f)) (erefl (Imp f0 f1)).
- move=>a b r IHr s IHs t IHt g c H.
  have [Hdr Hds Hdt] : [/\ derives g r (OrF a b), derives (a :: g) s c & derives (b :: g) t c].
  - by case: _ {1}_ _ / H (erefl (Cas a b r s t))=>// ?????????? [<-<-<-<-<-].
  by apply: cas=>//; [apply: IHr|apply: IHs|apply: IHt].
move=>r IH + a; case=>[|f g'] H.
- exfalso.
  by case: {-1}_ {1}_ {1}_ / H (erefl (@nil (form A))) (erefl (Shift r)).
have Hd: derives g' r a.
- by case: {-1}_ {1}_ {1}_ / H (erefl (f::g')) (erefl (Shift r))=>// ????? [_ ->][<-].
by apply: shift=>//; apply: IH.
Qed.

End Derivation.