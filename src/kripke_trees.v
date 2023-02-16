From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype seq order.
From ipcssr Require Import prelude avlmap trees forms derivations.

Section KripkeModel.
Context {A : Type} {I : eqType}.
Variables (le : rel A) (world : pred A) (forces0 : A -> I -> bool).

Fixpoint forces (k : A) (a : form I) : Prop :=
  match a with
  | Falsum     => False
  | Atom i     => forces0 k i
  | AndF a0 a1 => forces k a0 /\ forces k a1
  | OrF  a0 a1 => forces k a0 \/ forces k a1
  | Imp  a0 a1 =>
      forall k' : A, world k' -> le k k' ->
      forces k' a0 -> forces k' a1
  end.

Lemma forces_imp_trans :
  forall (k : A) (a b c : form I),
  forces k (Imp a b) ->
  forces k (Imp b c) ->
  forces k (Imp a c).
Proof.
move=>k a b c /= Fab Fbc k' W' L F'.
by apply: Fbc=>//; apply: Fab.
Qed.

Lemma forces_imp_or :
 forall (k : A) (a b c : form I),
 forces k (Imp a c) ->
 forces k (Imp b c) ->
 forces k (Imp (OrF a b) c).
Proof.
by move=>k a b c /= Fac Fbc k' W' L; case=>F'; [apply: Fac|apply: Fbc].
Qed.

Lemma forces_imp_drop_snd :
 forall (k : A) (a c : form I), forces k (Imp a c) ->
 forall b : form I, forces k (Imp (AndF a b) c).
Proof.
move=>k a c /= Fac b k' W' L [Fa _].
by apply: Fac.
Qed.

Lemma forces_imp_drop_fst :
 forall (k : A) (b c : form I),
 forces k (Imp b c) ->
 forall a : form I, forces k (Imp (AndF a b) c).
Proof.
move=>k b c /= Fbc a k' W' L [_ Fb].
by apply: Fbc.
Qed.

Definition World_refl : Prop :=
  forall k, world k -> le k k.

Definition World_trans : Prop :=
  forall k0 k1 k2, world k0 -> world k1 -> world k2 ->
    le k0 k1 ==> le k1 k2 ==> le k0 k2.

Definition World_mono : Prop :=
  forall k0 k1, world k0 -> world k1 -> le k0 k1 ->
    forall i, forces0 k0 i ==> forces0 k1 i.

Definition Kripke_Model : Prop :=
  [ /\ World_refl, World_trans & World_mono].

Lemma forces_mono :
  World_trans -> World_mono ->
  forall (k k': A) (a : form I),
  world k -> world k' -> le k k' ->
  forces k a -> forces k' a.
Proof.
move=>Wt Wm k k' + W; elim=>//=.
- move=>a W' L.
  by apply/implyP/Wm.
- by move=>al IHl ar IHr W' L [Hl Hr]; split; [apply: IHl | apply: IHr].
- by move=>al IHl ar IHr W' L; case=>H; [left; apply: IHl | right; apply: IHr].
move=>al IHl ar IHr W' L H k'' W'' L''.
by apply: H=>//; move: L''; apply/implyP; move: L; apply/implyP; apply: Wt.
Qed.

Lemma soundness g t a :
  Kripke_Model ->
  derives g t a ->
  forall k : A, world k -> {in g, forall c, forces k c} ->
  forces k a.
Proof.
case=>[Wr Wt Wm]; elim/(@derives_rec I)=>{g t a}/=.
- (* Var n *)
  by move=>g n a /onth_mem Ha k W; apply.
- (* Efq t a *)
  by move=>g t a H IH k W F; move: (IH _ W F).
- (* Abs a b *)
  move=>g a r b H IH k W F k' W' L F'.
  apply: IH=>// h; rewrite inE; case/orP=>[/eqP->|] // Hh.
  by apply: (forces_mono _ _ k)=>//; apply: F.
- (* App r s *)
  move=>g r s a b Hr IHr Hs IHs k W F.
  by apply: (IHr _ _ F)=>//; [apply: Wr | apply: IHs].
- (* Pair r s *)
  move=>f r s a b Hr IHr Hs IHs k W F.
  by split; [apply: IHr|apply: IHs].
- (* PrL r *)
  move=>g r a b H IH k W F.
  by case: (IH _ _ F).
- (* PrR r *)
  move=>g r a b H IH k W F.
  by case: (IH _ _ F).
- (* OrFL r b *)
  move=>g r a b H IH k W F.
  by left; apply: (IH _ _ F).
- (* OrFR r b *)
  move=>g r a b H IH k W F.
  by right; apply: (IH _ _ F).
- (* Cas r s t *)
  move=>g r s t a b c Hr IHr Hs IHs Ht IHt k W F.
  case: (IHr _ _ F)=>// Hc; [apply: IHs|apply: IHt]=>// q; rewrite inE; case/orP.
  - by move/eqP=>{q}->.
  - by move=>Hq; apply: F.
  - by move/eqP=>{q}->.
  - by move=>Hq; apply: F.
(* Shift r *)
move=>g r a b H IH k W F.
by apply: IH=>// z Hz; apply: F; rewrite inE Hz orbT.
Qed.

Lemma forces_uncurry :
  World_refl ->
  forall k : A,
  forall a b c : form I,
  forces k (Imp a (Imp b c)) -> forces k (Imp (AndF a b) c).
Proof.
move=>Wr k a b c /= F k' W' L [Fa Fb].
by apply: (F k')=>//; apply: Wr.
Qed.

Lemma forces_imp :
  World_trans -> World_mono ->
  forall k : A, world k ->
  forall b : form I, forces k b ->
  forall a : form I, forces k (Imp a b).
Proof.
move=>Wt Wm k W b Fb a /= k' W' L _.
by apply: (forces_mono _ _ k).
Qed.

Lemma forces_imp_imp_to :
  Kripke_Model ->
  forall k : A, world k ->
  forall a : form I, forces k a ->
  forall b c : form I,
  forces k (Imp b c) -> forces k (Imp (Imp a b) c).
Proof.
case=>[Wr Wt Wm] k W a Fa b c /= Fbc k' W' L F.
apply: Fbc=>//; apply: F=>//; first by apply: Wr.
by apply: (forces_mono _ _ k).
Qed.

Lemma forces_imp_imp_fro :
  World_trans -> World_mono ->
  forall k : A, world k ->
  forall a : form I, forces k a ->
  forall b c : form I,
  forces k (Imp (Imp a b) c) -> forces k (Imp b c).
Proof.
move=>Wt Wm k W a Fa b c /= Fabc k' W' L Fb.
apply: Fabc=>// k'' W'' L' F''.
by apply: (forces_mono _ _ k').
Qed.

End KripkeModel.

Section KripkeTree.
Context {disp : unit} {I : orderType disp}.

Definition atoms : Type := kvtree I unit.
Definition kripke_tree : Type := tree atoms.

(* lookup is coerced from option *)
Definition Is_Monotone_kripke_tree : kripke_tree -> Prop :=
  Is_Monotone_Tree lookup.

Definition Suc (k0 k1 : kripke_tree) : bool :=
  successor k0 k1.
Definition Atms (k : kripke_tree) : atoms :=
  root k.
Definition Succs (k0 : kripke_tree) : seq kripke_tree :=
  children_of_node k0.

Lemma kripke_tree_kripke_model :
 forall k, Is_Monotone_kripke_tree k ->
 Kripke_Model (fun k0 k1 => Suc k1 k0)          (* le *)
              (fun k0 => Suc k0 k)              (* world *)
              (fun k0 i => lookup (Atms k0) i). (* forces *)
Proof.
move=>k H; rewrite /Kripke_Model /World_refl /World_trans /World_mono /=; split.
- by move=>k1 _; apply: successor_refl.
- move=>k1 k2 k3 _ _ _; apply/implyP=>S21; apply/implyP=>S32.
  by apply/successor_trans/S21.
move=>k1 k2 S1 _ S21 i; rewrite /Atms.
by move/is_monotone_tree_is_monotone: H; apply.
Qed.

(*
Lemma kripke_tree_succ k k0 :
  Suc k0 k ->
  Is_Monotone_kripke_tree k -> Is_Monotone_kripke_tree k0.
Proof. by exact: successor_is_monotone_tree. Qed.
*)

Definition forces_t2 (k0 k : kripke_tree) (a : form I) : Prop :=
  forces (fun k1 k2 => Suc k2 k1)
         (fun k1 => Suc k1 k0)
         (fun k1 i => lookup (Atms k1) i) k a.

Lemma forces_t2_is_local a k :
  Is_Monotone_kripke_tree k ->
  forall k', Suc k' k ->
  forces_t2 k k' a ->
  forall k0 : kripke_tree,
  Is_Monotone_kripke_tree k0 -> Suc k' k0 -> forces_t2 k0 k' a.
Proof.
elim: a k=>//=.
- move=>l IHl r IHr k Mk k' S [Fl Fr] k0 H0 S0.
  by split; [apply: (IHl k)|apply: (IHr k)].
- move=>l IHl r IHr k Mk k' S Flr k0 H0 S0.
  case: Flr=>[Fl|Fr].
  - by left; apply: (IHl k).
  by right; apply: (IHr k).
move=>l IHl r IHr k Mk k' S Flr k0 H0 S0 k'' S1 S2 F''.
have S3 : Suc k'' k by apply/successor_trans/S.
apply: (IHr k)=>//; apply: Flr=>//.
by apply: (IHl k0).
Qed.

Definition forces_t (k : kripke_tree) : form I -> Prop :=
  forces_t2 k k.

Lemma forces_t_imp :
  forall k, Is_Monotone_kripke_tree k ->
  forall a b, (forces_t k a -> forces_t k b) ->
  {in Succs k, forall k', forces_t k' (Imp a b)} ->
  forces_t k (Imp a b).
Proof.
move=>k Mk a b Fab H; rewrite /forces_t /= => k' _ S'.
case/successorP: (S')=>/= [->|[t Ht St]] // Fa.
have Mt: Is_Monotone_kripke_tree t.
- apply: (successor_is_monotone_tree k)=>//.
  by apply/successorP=>/=; right; exists t=>//; exact: successor_refl.
apply: (forces_t2_is_local _ t)=>//.
move: (H t); rewrite /forces_t /=; apply=>//.
by apply: (forces_t2_is_local _ k).
Qed.

End KripkeTree.