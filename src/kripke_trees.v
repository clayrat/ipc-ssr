From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq order.
From ipcssr Require Import prelude avlmap trees forms derivations.

Section KripkeModel.
Context {T : Type} {A : eqType}.
Variables (le : rel T) (world : pred T) (forces0 : T -> A -> bool).

Fixpoint forces (t : T) (a : form A) : Prop :=
  match a with
  | Falsum     => False
  | Atom i     => forces0 t i
  | AndF a0 a1 => forces t a0 /\ forces t a1
  | OrF  a0 a1 => forces t a0 \/ forces t a1
  | Imp  a0 a1 =>
      forall t' : T, world t' -> le t t' ->
      forces t' a0 -> forces t' a1
  end.

Lemma forces_imp_trans t a b c :
  forces t (Imp a b) ->
  forces t (Imp b c) ->
  forces t (Imp a c).
Proof.
move=>/= Fab Fbc t' W' L F'.
by apply: Fbc=>//; apply: Fab.
Qed.

Lemma forces_imp_or t a b c :
  forces t (Imp a c) ->
  forces t (Imp b c) ->
  forces t (Imp (OrF a b) c).
Proof.
by move=>/= Fac Fbc t' W' L; case=>F'; [apply: Fac|apply: Fbc].
Qed.

Lemma forces_imp_drop_snd t a b c :
  forces t (Imp a c) -> forces t (Imp (AndF a b) c).
Proof.
move=>/= Fac t' W' L [Fa _].
by apply: Fac.
Qed.

Lemma forces_imp_drop_fst t a b c :
  forces t (Imp b c) -> forces t (Imp (AndF a b) c).
Proof.
move=>/= Fbc t' W' L [_ Fb].
by apply: Fbc.
Qed.

Lemma forces_imp_and t a b c :
  forces t (Imp a b) -> forces t (Imp a c) -> forces t (Imp a (AndF b c)).
Proof.
move=>/= Fab Fac t' W' L Fa.
by split; [apply: Fab | apply: Fac].
Qed.

Lemma forces_imp_or_false_l t a b :
  forces t (Imp a b) -> forces t (Imp a (OrF Falsum b)).
Proof.
move=>/=Fab t' W' L Fa; right.
by apply: Fab.
Qed.

Lemma forces_imp_or_false_r t a b :
  forces t (Imp a b) -> forces t (Imp a (OrF b Falsum)).
Proof.
move=>/=Fab t' W' L Fa; left.
by apply: Fab.
Qed.

Lemma forces_imp_imp_false_l t a b :
  forces t (Imp a (Imp Falsum b)).
Proof. by move=>//=. Qed.

Lemma forces_imp_imp_false_r t a b c :
  forces t (Imp (Imp a b) c) -> forces t (Imp (Imp a Falsum) c).
Proof.
move=>/= Fabc t' W' L Faf.
apply: Fabc=>// t'' W'' L' Fa.
by exfalso; apply: (Faf t'').
Qed.

Definition World_refl : Prop :=
  forall t, world t -> le t t.

Definition World_trans : Prop :=
  forall k0 k1 k2, world k0 -> world k1 -> world k2 ->
    le k0 k1 ==> le k1 k2 ==> le k0 k2.

Definition World_mono : Prop :=
  forall k0 k1, world k0 -> world k1 -> le k0 k1 ->
    forall i, forces0 k0 i ==> forces0 k1 i.

Definition Kripke_Model : Prop :=
  [/\ World_refl, World_trans & World_mono].

Lemma forces_mono :
  World_trans -> World_mono ->
  forall (t t': T) (a : form A),
  world t -> world t' -> le t t' ->
  forces t a -> forces t' a.
Proof.
move=>Wt Wm t t' + W; elim=>//=.
- move=>a W' L.
  by apply/implyP/Wm.
- by move=>al IHl ar IHr W' L [Hl Hr]; split; [apply: IHl | apply: IHr].
- by move=>al IHl ar IHr W' L; case=>H; [left; apply: IHl | right; apply: IHr].
move=>al IHl ar IHr W' L H t'' W'' L''.
by apply: H=>//; move: L''; apply/implyP; move: L; apply/implyP; apply: Wt.
Qed.

Lemma soundness g t a :
  Kripke_Model ->
  derives g t a ->
  forall q : T, world q -> {in g, forall c, forces q c} ->
  forces q a.
Proof.
case=>[Wr Wt Wm]; elim/(@derives_rec A)=>{g t a}/=.
- (* Var n *)
  by move=>g n a /onth_mem Ha q W; apply.
- (* Efq t a *)
  by move=>g t a H IH q W F; move: (IH _ W F).
- (* Abs a b *)
  move=>g a r b H IH q W F q' W' L F'.
  apply: IH=>// h; rewrite inE; case/orP=>[/eqP->|] // Hh.
  by apply: (forces_mono _ _ q)=>//; apply: F.
- (* App r s *)
  move=>g r s a b Hr IHr Hs IHs q W F.
  by apply: (IHr _ _ F)=>//; [apply: Wr | apply: IHs].
- (* Pair r s *)
  move=>f r s a b Hr IHr Hs IHs q W F.
  by split; [apply: IHr|apply: IHs].
- (* PrL r *)
  move=>g r a b H IH q W F.
  by case: (IH _ _ F).
- (* PrR r *)
  move=>g r a b H IH q W F.
  by case: (IH _ _ F).
- (* OrFL r b *)
  move=>g r a b H IH q W F.
  by left; apply: (IH _ _ F).
- (* OrFR r b *)
  move=>g r a b H IH q W F.
  by right; apply: (IH _ _ F).
- (* Cas r s t *)
  move=>g r s t a b c Hr IHr Hs IHs Ht IHt q W F.
  case: (IHr _ _ F)=>// Hc; [apply: IHs|apply: IHt]=>// z; rewrite inE; case/orP.
  - by move/eqP=>{z}->.
  - by move=>Hz; apply: F.
  - by move/eqP=>{z}->.
  - by move=>Hz; apply: F.
(* Shift r *)
move=>g r a b H IH q W F.
by apply: IH=>// z Hz; apply: F; rewrite inE Hz orbT.
Qed.

Lemma forces_uncurry t a b c :
  World_refl ->
  forces t (Imp a (Imp b c)) -> forces t (Imp (AndF a b) c).
Proof.
move=>Wr /= F t' W' L [Fa Fb].
by apply: (F t')=>//; apply: Wr.
Qed.

Lemma forces_imp t a b :
  World_trans -> World_mono ->
  world t ->
  forces t b -> forces t (Imp a b).
Proof.
move=>Wt Wm W Fb /= t' W' L _.
by apply: (forces_mono _ _ t).
Qed.

Lemma forces_imp_imp_to t a b c :
  Kripke_Model ->
  world t ->
  forces t a -> forces t (Imp b c) ->
  forces t (Imp (Imp a b) c).
Proof.
case=>[Wr Wt Wm] W Fa /= Fbc t' W' L F.
apply: Fbc=>//; apply: F=>//; first by apply: Wr.
by apply: (forces_mono _ _ t).
Qed.

Lemma forces_imp_imp_fro t a b c :
  World_trans -> World_mono ->
  world t ->
  forces t a -> forces t (Imp (Imp a b) c) ->
  forces t (Imp b c).
Proof.
move=>Wt Wm W Fa /= Fabc t' W' L Fb.
apply: Fabc=>// t'' W'' L' F''.
by apply: (forces_mono _ _ t').
Qed.

Lemma forces_imp_app t a b :
  World_refl ->
  world t ->
  forces t a -> forces t (Imp a b) -> forces t b.
Proof. by move=>Wr W Fa; apply=>//; apply: Wr. Qed.

Lemma forces_vimp t (s : seq A) a b :
  World_refl -> World_trans ->
  world t ->
  (forall t', world t' -> le t t' -> forces t' a -> forces t' b) ->
  forces t (vimp s a) -> forces t (vimp s b).
Proof.
move=>Wr Wt W; elim: s=>/= [|h s IH] in a b *; move=>H.
- by apply/H/Wr.
apply: IH=>t' W' L /= Fia t'' W'' L' Fh.
apply: H=>//; last by apply: Fia.
move: L'; apply/implyP; move: L; apply/implyP.
by apply: Wt.
Qed.

Lemma forces_vimp2 t (s : seq A) a b c :
  World_refl -> World_trans ->
  world t ->
  (forall t', world t' -> le t t' ->
     forces t' a -> forces t' b -> forces t' c) ->
  forces t (vimp s a) -> forces t (vimp s b) -> forces t (vimp s c).
Proof.
move=>Wr Wt W; elim: s=>/= [|h s IH] in a b c *; move=>H.
- by apply/H/Wr.
apply: IH=>t' W' L /= Fia Fib t'' W'' L' Fh.
apply: H=>//.
- move: L'; apply/implyP; move: L; apply/implyP.
  by apply: Wt.
- by apply: Fia.
by apply: Fib.
Qed.

Lemma forces_vimp0 t (s : seq A) a :
  World_refl -> World_trans ->
  world t ->
  (forall t', world t' -> le t t' -> forces t' a) ->
  forces t (vimp s a).
Proof.
move=>Wr Wt W; elim: s=>/= [|h s IH] in a *; move=>H.
- by apply/H/Wr.
apply: IH=>t' W' L /= t'' W'' L' Fh; apply: H=>//.
move: L'; apply/implyP; move: L; apply/implyP.
by apply: Wt.
Qed.

End KripkeModel.

Section KripkeTree.
Context {disp : unit}.

(************************************************************************)
(* Atoms are stored in AVL Trees ai over unit.                          *)
(* For the node with the key field=i,                                   *)
(* we define that (Atom i) is in ai.                                    *)
(************************************************************************)

Definition atoms (A : orderType disp) : Type := kvtree A unit.
Definition kripke_tree (A : orderType disp) : Type := tree (atoms A).

Context {A : orderType disp}.

Definition update_atoms (i : A) := upsert i (fun=>tt) tt.

(* lookup is coerced from option *)
Definition Is_Monotone_kripke_tree : kripke_tree A -> Prop :=
  Is_Monotone_Tree lookup.

Definition Suc (k0 k1 : kripke_tree A) : bool :=
  successor k0 k1.
Definition Atms (t : kripke_tree A) : atoms A :=
  root t.
Definition Succs (k0 : kripke_tree A) : seq (kripke_tree A) :=
  children_of_node k0.

Definition kt_le k0 k1 := Suc k1 k0.
Definition kt_world := kt_le.
Definition kt_forces k0 := lookup (Atms k0).

Lemma kripke_tree_world_refl t :
  World_refl kt_le (kt_world t).
Proof. by rewrite /World_refl=>{}t _; exact: successor_refl. Qed.

Lemma kripke_tree_world_trans t :
  World_trans kt_le (kt_world t).
Proof.
rewrite /World_trans=>k1 k2 k3 _ _ _; apply/implyP=>S21; apply/implyP=>S32.
by apply/successor_trans/S21.
Qed.

Lemma kripke_tree_world_mono t :
  Is_Monotone_kripke_tree t ->
  World_mono kt_le (kt_world t) kt_forces.
Proof.
rewrite /World_mono=>H k1 k2 S1 _ S21 i; rewrite /Atms.
by move/is_monotone_tree_is_monotone: H; apply.
Qed.

Lemma kripke_tree_kripke_model t :
  Is_Monotone_kripke_tree t ->
  Kripke_Model kt_le (kt_world t) kt_forces.
Proof.
move=>H; split.
- exact: kripke_tree_world_refl.
- exact: kripke_tree_world_trans.
by apply: kripke_tree_world_mono.
Qed.

Definition forces_t2 (k0 t : kripke_tree A) (a : form A) : Prop :=
  forces kt_le (kt_world k0) kt_forces t a.

Lemma forces_t2_is_local a t :
  Is_Monotone_kripke_tree t ->
  forall t', Suc t' t ->
  forces_t2 t t' a ->
  forall k0,
  Is_Monotone_kripke_tree k0 -> Suc t' k0 -> forces_t2 k0 t' a.
Proof.
elim: a t=>//=.
- move=>l IHl r IHr t Mk t' S [Fl Fr] k0 H0 S0.
  by split; [apply: (IHl t)|apply: (IHr t)].
- move=>l IHl r IHr t Mk t' S Flr k0 H0 S0.
  case: Flr=>[Fl|Fr].
  - by left; apply: (IHl t).
  by right; apply: (IHr t).
move=>l IHl r IHr t Mk t' S Flr k0 H0 S0 t'' S1 S2 F''.
have S3 : Suc t'' t by apply/successor_trans/S.
apply: (IHr t)=>//; apply: Flr=>//.
by apply: (IHl k0).
Qed.

Definition forces_t (t : kripke_tree A) : form A -> Prop :=
  forces_t2 t t.

Lemma forces_t_imp t :
  Is_Monotone_kripke_tree t ->
  forall a b, (forces_t t a -> forces_t t b) ->
  {in Succs t, forall t', forces_t t' (Imp a b)} ->
  forces_t t (Imp a b).
Proof.
move=>Mk a b Fab H; rewrite /forces_t /= => t' _ S'.
case/successorP: (S')=>/= [->|[q Hq Sq]] // Fa.
have Mt: Is_Monotone_kripke_tree q.
- apply: (successor_is_monotone_tree t)=>//.
  by apply/successorP=>/=; right; exists q=>//; exact: successor_refl.
apply: (forces_t2_is_local _ q)=>//.
move: (H q); rewrite /forces_t /=; apply=>//.
by apply: (forces_t2_is_local _ t).
Qed.

Lemma forces_t_mon t :
  Is_Monotone_kripke_tree t ->
  forall t', Suc t' t ->
  forall a, forces_t t a -> forces_t t' a.
Proof.
move=>Mk t' S a F; rewrite /forces_t.
apply: (forces_t2_is_local _ t)=>//.
- case/kripke_tree_kripke_model: Mk=>Wr Wt Wm.
  by apply: (forces_mono _ _ _ _ _ t)=>//; exact: successor_refl.
- by apply: (successor_is_monotone_tree t)=>//.
by exact: successor_refl.
Qed.

Lemma soundness_t g t a :
  derives g t a ->
  forall q, Is_Monotone_kripke_tree q ->
  {in g, forall c, forces_t q c} -> forces_t q a.
Proof.
move=>D q Mk H; rewrite /forces_t.
apply: (soundness _ _ _ g t)=>//; last by exact: successor_refl.
by apply: kripke_tree_kripke_model.
Qed.

Lemma forces_imp_t t a b :
  Is_Monotone_kripke_tree t ->
  forces_t t b -> forces_t t (Imp a b).
Proof.
case/kripke_tree_kripke_model=>[_ Wt Wm].
by apply: forces_imp=>//; exact: successor_refl.
Qed.

Lemma forces_uncurry_t t a b c :
  forces_t t (Imp a (Imp b c)) -> forces_t t (Imp (AndF a b) c).
Proof. by apply: forces_uncurry; exact: kripke_tree_world_refl. Qed.

Lemma forces_imp_imp_to_t t a b c :
  Is_Monotone_kripke_tree t ->
  forces_t t a -> forces_t t (Imp b c) ->
  forces_t t (Imp (Imp a b) c).
Proof.
move/kripke_tree_kripke_model=>K.
by apply: forces_imp_imp_to=>//; exact: successor_refl.
Qed.

Lemma forces_imp_imp_fro_t t a b c :
  Is_Monotone_kripke_tree t ->
  forces_t t a -> forces_t t (Imp (Imp a b) c) ->
  forces_t t (Imp b c).
Proof.
case/kripke_tree_kripke_model=>_ Wt Wm.
apply: forces_imp_imp_fro=>//.
by exact: successor_refl.
Qed.

Lemma forces_imp_app_t t a b :
  forces_t t a -> forces_t t (Imp a b) -> forces_t t b.
Proof.
apply: forces_imp_app.
- by exact: kripke_tree_world_refl.
by exact: successor_refl.
Qed.

Lemma forces_vimp_t t (s : seq A) a b :
  (forall t', Suc t' t -> forces_t2 t t' a -> forces_t2 t t' b) ->
  forces_t t (vimp s a) -> forces_t t (vimp s b).
Proof.
rewrite /forces_t=>H; apply: forces_vimp.
- by exact: kripke_tree_world_refl.
- by exact: kripke_tree_world_trans.
- by exact: successor_refl.
by move=>t' _ S; apply: H.
Qed.

Lemma forces_vimp2_t t (s : seq A) a b c :
  (forall t', Suc t' t ->
    forces_t2 t t' a -> forces_t2 t t' b -> forces_t2 t t' c) ->
  forces_t t (vimp s a) -> forces_t t (vimp s b) -> forces_t t (vimp s c).
Proof.
rewrite /forces_t=>H; apply: forces_vimp2.
- by exact: kripke_tree_world_refl.
- by exact: kripke_tree_world_trans.
- by exact: successor_refl.
by move=>t' _ S; apply: H.
Qed.

Lemma forces_vimp0_t t (s : seq A) a  :
  (forall t', Suc t' t -> forces_t2 t t' a) ->
  forces_t t (vimp s a).
Proof.
rewrite /forces_t=>H; apply: forces_vimp0.
- by exact: kripke_tree_world_refl.
- by exact: kripke_tree_world_trans.
- by exact: successor_refl.
by move=>t' _ S; apply: H.
Qed.

End KripkeTree.
