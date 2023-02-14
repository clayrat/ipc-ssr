From Coq Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import eqtype ssrnat order seq path.
From ipcssr Require Import prelude.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.POrderTheory.
Import Order.TotalTheory.
Open Scope order_scope.

Module Map.
Structure Map (K : eqType) (V : Type) : Type :=
  make {tp :> Type;
        empty : tp;
        update : K -> V -> tp -> tp;
        delete : K -> tp -> tp;
        lookup : tp -> K -> option V;

        invar : tp -> bool;

        _ : invar empty;
        _ : lookup empty =1 fun => None;

        _ : forall k v s, invar s -> invar (update k v s);
        _ : forall k v s, invar s ->
            lookup (update k v s) =1 [eta (lookup s) with k |-> Some v];

        _ : forall k s, invar s -> invar (delete k s);
        _ : forall k s, invar s ->
            lookup (delete k s) =1 [eta (lookup s) with k |-> None]
        }.
End Map.

Section Cmp.
Context {disp : unit} {T : orderType disp}.

Variant cmp_val := LT | EQ | GT.

Definition cmp (x y : T) : cmp_val :=
  if x < y then LT else if x == y then EQ else GT.

Lemma cmpxx x : cmp x x = EQ.
Proof. by rewrite /cmp eqxx ltxx. Qed.

Variant cmp_spec (x y : T) : cmp_val -> cmp_val -> bool -> bool -> bool -> bool -> Set :=
  | CmpLt of x < y : cmp_spec x y LT GT true  false false false
  | CmpEq of x = y : cmp_spec x y EQ EQ false true  true  false
  | CmpGt of x > y : cmp_spec x y GT LT false false false true.

Lemma cmpE (x y : T) : cmp_spec x y (cmp x y) (cmp y x) (x < y) (x == y) (y == x) (y < x).
Proof. by rewrite /cmp; case: ltgtP=>H; constructor. Qed.

End Cmp.

Section KVList.
Context {disp : unit} {K : orderType disp} {V : Type}.

Fixpoint find_list (k : K) (xs : seq (K*V)) : option V :=
  if xs is (k0,v)::xs' then
    match cmp k k0 with
    | LT => None
    | EQ => Some v
    | GT => find_list k xs'
    end
  else None.

Fixpoint ins_list (k : K) (v : V) (xs : seq (K*V)) : seq (K*V) :=
  if xs is (k0,v0)::xs' then
    match cmp k k0 with
    | LT => (k,v) :: (k0,v0) :: xs'
    | EQ => (k,v) :: xs'
    | GT => (k0,v0) :: ins_list k v xs'
    end
  else [::(k,v)].

Fixpoint del_list (k : K) (xs : seq (K*V)) : seq (K*V) :=
  if xs is (k0,v0) :: xs' then
    if k == k0 then xs'
      else (k0,v0) :: del_list k xs'
  else [::].

Lemma findlist_sorted_cat_cons_cat (xs ys : seq (K*V)) k k' v' :
  sorted <%O (map fst (xs ++ (k',v') :: ys)) ->
  find_list k (xs ++ (k',v') :: ys) = if k < k'
                                       then find_list k xs
                                       else find_list k ((k',v') :: ys).
Proof.
elim: xs=>/=; first by move=>H; case: cmpE.
case=>k0 v0 xs /= + H; rewrite map_cat /= in H.
move: (H); move/(order_path_min lt_trans).
rewrite map_cat all_cat /= =>/and3P [Hxs Hya Hys].
case: cmpE=>Hk.
- case: cmpE (lt_trans Hya Hk)=>// Hk0 _; apply.
  by move/path_sorted: H.
- rewrite -Hk; case: cmpE Hya=>// Hya _; apply.
  by move/path_sorted: H.
case: cmpE=>// H0; apply.
by move/path_sorted: H.
Qed.

Lemma inorder_ins_list k v xs :
  sorted <%O (map fst xs) ->
  perm_eq (map fst (ins_list k v xs))
          (if k \in map fst xs then map fst xs else k :: map fst xs).
Proof.
elim: xs=>//=[[k0 v0]] xs IH /= Hp.
rewrite inE; case: cmpE=>Hk /=.
- move/path_sorted: Hp=>/IH; case: ifP=>H; first by rewrite perm_cons.
  by move=>H1; rewrite perm_sym -cat1s -(cat1s k0) perm_catCA /= perm_cons perm_sym.
- by rewrite Hk.
case: ifP=>//; move: (order_path_min lt_trans Hp)=>/allP/[apply].
by rewrite ltNge le_eqVlt Hk orbT.
Qed.

Lemma ins_list_sorted k v xs :
  sorted <%O (map fst xs) -> sorted <%O (map fst (ins_list k v xs)).
Proof.
elim: xs=>//=[[k0 v0]] xs /= IH H.
case: cmpE=>Hk //=.
- move: H; rewrite !(path_sortedE lt_trans); case/andP=>H1 /[dup] H2 /IH->; rewrite andbT.
  rewrite (perm_all _ (inorder_ins_list _ _ H2)); case: ifP=>//= _.
  by rewrite Hk.
- by rewrite -Hk.
by rewrite Hk.
Qed.

Lemma inslist_sorted_cat_cons_cat (xs ys : seq (K*V)) k v k' v' :
  sorted <%O (map fst (xs ++ [::(k',v')])) ->
  ins_list k v (xs ++ (k',v') :: ys) = if k < k'
                                         then ins_list k v xs ++ (k',v') :: ys
                                         else xs ++ ins_list k v ((k',v') :: ys).
Proof.
elim: xs=>/=; first by move=>_; case: (cmpE k k').
move=>[k0 v0] /= xs + H; rewrite map_cat /= in H.
move: (H); move/(order_path_min lt_trans).
rewrite map_cat all_cat /= andbT =>/andP [Hxs Hya].
case: (cmpE k k')=>H'.
- case: (cmpE k k0)=>// H0 -> //.
  by apply: (path_sorted H).
- rewrite {k}H'; case: (cmpE k' k0) Hya=>// Hya _ -> //.
  by apply: (path_sorted H).
case: (cmpE k k0) (lt_trans Hya H')=>// H0 _ -> //.
by apply: (path_sorted H).
Qed.

Lemma find_ins_list_same k v xs : find_list k (ins_list k v xs) = Some v.
Proof.
elim: xs=>/=; first by rewrite cmpxx.
case=>k0 v0 xs IH; case: cmpE=>Hk /=.
- by case: cmpE Hk.
- by rewrite cmpxx.
by rewrite cmpxx.
Qed.

Lemma find_ins_list_diff q k v xs :
  q != k ->
  find_list q (ins_list k v xs) = find_list q xs.
Proof.
elim: xs=>/=; first by case: cmpE.
case=>k0 v0 xs IH H; case: cmpE=>Hk /=.
- by case: cmpE=>// H0; apply: IH.
- by rewrite Hk; case: cmpE=>// E; rewrite E eqxx in H.
by case: cmpE H=>// Hq _; case: cmpE (lt_trans Hq Hk).
Qed.

Lemma del_nop k xs :
  path <%O k (map fst xs) -> del_list k xs = xs.
Proof.
elim: xs=>//= [[k0 v0]] xs IH /= /andP [H1 H2].
case: ltgtP H1=>// H1 _; rewrite IH //.
by apply/(path_le lt_trans)/H2.
Qed.

Lemma dellist_sorted_cat_cons_cat (xs ys : seq (K*V)) k k' v' :
  sorted <%O (map fst (xs ++ (k',v') :: ys)) ->
  del_list k (xs ++ (k',v') :: ys) = if k < k'
                                       then del_list k xs ++ (k',v') :: ys
                                       else xs ++ del_list k ((k',v') :: ys).
Proof.
elim: xs=>/=.
- move=>H; case: ifP=>[/eqP->|_]; first by rewrite ltxx.
  case: ifP=>// Hx.
  by rewrite del_nop //; apply/(path_le lt_trans)/H.
case=>k0 v0 xs /= + H; rewrite map_cat /= in H.
move: (H); move/(order_path_min lt_trans).
rewrite map_cat all_cat /= =>/and3P [Hxs Hya Hys].
case: ifP.
- move=>Ha; case: ifP=>// /negbT Hy.
  by move=>-> //; apply: (path_sorted H).
move=>/negbT Ha; case: ifP.
- move/eqP=>{Ha}->; case: ifP=>/=.
  - by move/eqP=>Hay; rewrite Hay ltxx in Hya.
  by move=>_ ->//; apply: (path_sorted H).
move/negbT=>Ha'; move: Ha; rewrite lt_neqAle Ha' /= -ltNge=>{Ha'}Hx.
case: ifP.
- move/eqP=>He; rewrite He in Hx; move: Hx.
  by rewrite ltNge le_eqVlt Hya orbT.
by move/negbT=>_ -> //; apply: (path_sorted H).
Qed.

End KVList.

Section AVLMap.
Context {disp : unit} {K : orderType disp} {V : Type}.

Variant bal := Lh | Bal | Rh.

Definition eqbal (b1 b2 : bal) :=
  match b1, b2 with
  | Lh, Lh => true
  | Bal, Bal => true
  | Rh, Rh => true
  | _, _ => false
  end.

Lemma eqbalP : Equality.axiom eqbal.
Proof. by move; case; case; constructor. Qed.

Canonical bal_eqMixin := EqMixin eqbalP.
Canonical bal_eqType := Eval hnf in EqType bal bal_eqMixin.

Inductive kvtree K V := Leaf | Node of (kvtree K V) & K & V & bal & (kvtree K V).

Definition leaf : kvtree K V := @Leaf K V.

Definition is_node (t : kvtree K V) :=
  if t is Node _ _ _ _ _ then true else false.

Fixpoint height (t : kvtree K V) : nat :=
  if t is Node l _ _ _ r
    then maxn (height l) (height r) + 1
  else 0.

Lemma heightE (t : kvtree K V) : reflect (t = leaf) (height t == 0).
Proof.
apply: (iffP idP); last by move=>->.
by case: t=>//= l k v b r; rewrite addn1 => /eqP.
Qed.

Definition bal_inv (x : nat) (b : bal) (y : nat) : bool :=
  match b with
  | Lh => x == y + 1
  | Bal => y == x
  | Rh => y == x + 1
  end.

Fixpoint avl (t : kvtree K V) : bool :=
  if t is Node l _ _ b r then
    [&& bal_inv (height l) b (height r), avl l & avl r]
    else true.

Lemma avl_ind (P : kvtree K V -> Prop) :
  P (Leaf K V) ->
  (forall l k v b r,
   bal_inv (height l) b (height r) ->
   avl l -> avl r ->
   P l -> P r ->
   P (Node l k v b r)) ->
  forall t, avl t -> P t.
Proof.
move=>Pl Pn; elim=>//= l IHl k v b r IHr /and3P [H Hal Har].
by apply: Pn=>//; [apply: IHl| apply: IHr].
Qed.

Arguments avl_ind [P].

Definition is_bal (t : kvtree K V) : bool :=
  if t is Node _ _ _ b _ then b == Bal else false.

Definition incr (t t' : kvtree K V) : bool :=
  ~~ is_node t || (is_bal t && ~~ is_bal t').

(* leaf cases are essentially placeholders for totatity *)

Definition rot2 (a : kvtree K V) (xk : K) (xv : V)
                (b : kvtree K V) (zk : K) (zv : V)
                (c : kvtree K V) : kvtree K V :=
  match b with
  | Node b1 yk yv bb b2 =>
    let bb1 := if bb == Rh then Lh else Bal in
    let bb2 := if bb == Lh then Rh else Bal in
    Node (Node a xk xv bb1 b1) yk yv Bal (Node b2 zk zv bb2 c)
  | Leaf => Node a xk xv Bal (Node leaf zk zv Bal c)
  end.

Definition bLh (ab : kvtree K V) (zk : K) (zv : V) (c : kvtree K V) : kvtree K V :=
  match ab with
  | Node a xk xv Lh  b => Node a xk xv Bal (Node b zk zv Bal c)
  | Node a xk xv Bal b => Node a xk xv Rh  (Node b zk zv Lh  c)
  | Node a xk xv Rh  b => rot2 a xk xv b           zk zv c
  | Leaf               => Node leaf zk zv Bal c
  end.

Definition balL (ab : kvtree K V) (zk : K) (zv : V) (bb : bal) (c : kvtree K V) : kvtree K V :=
  match bb with
  | Lh  => bLh  ab zk zv     c
  | Bal => Node ab zk zv Lh  c
  | Rh  => Node ab zk zv Bal c
  end.

Definition bRh (a : kvtree K V) (xk : K) (xv : V) (bc : kvtree K V) : kvtree K V :=
  match bc with
  | Node b zk zv Lh  c => rot2 a xk xv b zk zv c
  | Node b zk zv Bal c => Node (Node a xk xv Rh  b) zk zv Lh  c
  | Node b zk zv Rh  c => Node (Node a xk xv Bal b) zk zv Bal c
  | Leaf               => Node a xk xv Bal leaf
  end.

Definition balR (a : kvtree K V) (xk : K) (xv : V) (bb : bal) (bc : kvtree K V) : kvtree K V :=
  match bb with
  | Lh  => Node a xk xv Bal bc
  | Bal => Node a xk xv Rh  bc
  | Rh  => bRh  a xk xv     bc
  end.

Fixpoint lookup (t : kvtree K V) (k : K) : option V :=
  if t is Node l k0 v0 _ r
    then match cmp k k0 with
           | LT => lookup l k
           | EQ => Some v0
           | GT => lookup r k
         end
  else None.

Fixpoint upsert (k : K) (v : V) (t : kvtree K V) : kvtree K V :=
  if t is Node l k0 v0 b r
    then match cmp k k0 with
         | LT => let l' := upsert k v l in
                 if incr l l' then balL l' k0 v0 b r else Node l' k0 v0 b r
         | EQ => Node l k v b r
         | GT => let r' := upsert k v r in
                 if incr r r' then balR l k0 v0 b r' else Node l k0 v0 b r'
         end
    else Node leaf k v Bal leaf.

Lemma avl_upsert k v t :
  avl t ->
  avl (upsert k v t) && (height (upsert k v t) == height t + incr t (upsert k v t)).
Proof.
elim/avl_ind=>//= l k0 v0 b r E Hl Hr /andP [Hal Hhl] /andP [Har Hhr].
case: (cmp k k0)=>/=.
- (* k < k0 *)
  case: ifP=>/= Hi; last first.
  - case: b E=>/=; move/eqP: Hhl=>->/eqP->;
    by rewrite Hi !addn0 Hal Hr !eq_refl.
  (* incr l insert *)
  rewrite Hi /= in Hhl.
  case: b E=>/eqP E /=.
  - (* b = Lh *)
    case E': (upsert k v l) Hi => [|li ki vi bi ri]/=.
    - (* insert = Leaf, impossible *)
      by rewrite E' addn1 in Hhl.
    (* insert = Node *)
    move: Hal Hhl; rewrite {}E' E /= maxn_addl addn0; case: bi=>/=.
    - (* bi = Lh *)
      case/and3P=>/eqP->->->/=.
      by rewrite maxn_addl !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eqxx.
    - (* bi = Bal *)
      case: {Hl}l E; rewrite /incr /=; first by rewrite addn1.
      by move=>????; rewrite andbF.
    (* bi = Rh *)
    case/and3P; case: ri=>/=; first by rewrite addn1; move/eqP.
    move=>lri kri vri bri rri /=; rewrite eqn_add2r /bal_inv =>/eqP <- ->.
    case: bri=>/= /and3P [/eqP->->->] /=.
    - (* bri = Lh *)
      rewrite -!addn_maxl maxn_addl -addn_maxl maxn_addr !eqn_add2r =>/eqP <-.
      by rewrite maxn_addr !maxnn Hr !eq_refl.
    - (* bri = Bal *)
      by rewrite !maxnn maxn_addr !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eq_refl.
    (* bri = Rh *)
    by rewrite !maxn_addr maxn_addl !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eq_refl.
  - (* b = Bal *)
    by rewrite Hal Hr; move/eqP: Hhl=>->; rewrite E maxnn maxn_addl !eq_refl.
  (* b = Rh *)
  by rewrite Hal Hr; move/eqP: Hhl=>->; rewrite E maxnn addn0 maxn_addr !eq_refl.
- (* k == k0 *)
  by rewrite Hl Hr /= andbT; case: b E=>/= /eqP->; rewrite addn0 !eq_refl.
(* k > k0 *)
case: ifP=>/=; last first.
- move=>Hi; case: b E=>/=; move/eqP: Hhr=>->/eqP->;
  by rewrite Hi !addn0 Har Hl !eq_refl.
(* incr r insert *)
move=>Hi; case: b E=>/eqP E /=.
- (* b = Lh *)
  by rewrite Har Hl; move/eqP: Hhr=>->; rewrite Hi E maxnn addn0 maxn_addl !eq_refl.
- (* b = Bal *)
  by rewrite Har Hl; move/eqP: Hhr=>->; rewrite Hi E maxnn maxn_addr !eq_refl.
(* b = Rh *)
case E': (upsert k v r)=> [|li ki vi bi ri]/=.
- (* insert = Leaf, impossible *)
  move: Hhr; rewrite E' /=; case: (incr _ _)=>/= /eqP; first by rewrite addn1.
  by rewrite addn0 E addn1.
(* insert = Node *)
move: Hi Har Hhr; rewrite {}E' E=>/=.
rewrite maxn_addr addn0; case: bi=>/=.
- (* bi = Lh *)
  move=>->; case/and3P; case: li=>/=; first by rewrite addn1; move/eqP.
  move=>lli kli vli bli rli /=; rewrite eqn_add2r /bal_inv =>/eqP <- /[swap] ->.
  case: bli=>/= /and3P [/eqP->->->] /=.
  - (* bli = Lh *)
    by rewrite !maxn_addl maxn_addr -addn_maxl !eqn_add2r =>/eqP=><-; rewrite !maxnn Hl !eq_refl.
  - (* bli = Bal *)
    by rewrite !maxnn maxn_addl !eqn_add2r =>/eqP<-; rewrite !maxnn Hl !eq_refl.
  (* bli = Rh *)
  rewrite maxn_addl maxn_addr -!addn_maxl !eqn_add2r=>/eqP<-.
  by rewrite maxn_addl !maxnn Hl !eq_refl.
- (* bi = Bal, impossible *)
  case: {Hr}r E; rewrite /incr /=; first by rewrite addn1.
  by move=>????; rewrite andbF.
(* bi = Rh *)
move=>->; case/and3P=>/eqP->->->/=.
by rewrite !eqn_add2r maxn_addr eqn_add2r=>/eqP<-; rewrite !maxnn Hl !eq_refl.
Qed.

Definition decr (t t' : kvtree K V) : bool :=
  is_node t && (~~ is_node t' || ((~~ is_bal t) && is_bal t')).

Fixpoint split_max (l : kvtree K V) (k : K) (v : V) (ba : bal) (r : kvtree K V) : kvtree K V * K * V :=
  if r is Node lr kr vr br rr
    then let: (r', k', v') := split_max lr kr vr br rr in
         let t' := if decr r r' then balL l k v ba r' else Node l k v ba r' in
         (t', k', v')
    else (l, k, v).

Fixpoint delete (k : K) (t : kvtree K V) : kvtree K V :=
  if t is Node l k0 v0 ba r
    then match cmp k k0 with
         | LT => let l' := delete k l in
                 if decr l l' then balR l' k0 v0 ba r else Node l' k0 v0 ba r
         | EQ => if l is Node ll kl vl bl rl then
                   let: (l', k', v') := split_max ll kl vl bl rl in
                   if decr l l' then balR l' k' v' ba r
                                else Node l' k' v' ba r
                   else r
         | GT => let r' := delete k r in
                 if decr r r' then balL l k0 v0 ba r' else Node l k0 v0 ba r'
         end
    else leaf.

Lemma avl_balL_decr (l : kvtree K V) k v b r t :
  avl l -> avl r -> bal_inv (height l) b (height r + 1) ->
  avl (balL l k v b r) && (maxn (height l) (height r + 1) + 1 == height (balL l k v b r) +
                                                                 decr (Node l k v b t) (balL l k v b r)).
Proof.
move=>Hl Hr; case: b=>/=.
- case: l Hl=>/=; first by move=>_ /eqP; rewrite addn1.
  move=>ll kl vl bl rl /and3P [Hbl Hall Harl].
  rewrite eqn_add2r => /[dup] H' /eqP ->; rewrite -addn_maxl maxn_addl.
  case: bl Hbl=>/=; move: (H')=>/[swap]/eqP->.
  - rewrite maxn_addl !eqn_add2r=>/eqP->.
    by rewrite !maxnn !eq_refl Hall Harl Hr.
  - rewrite maxnn addn0 !eqn_add2r=>/eqP->.
    by rewrite -addn_maxl maxn_addl maxn_addr !eq_refl Hall Harl Hr.
  rewrite maxn_addr eqn_add2r =>/eqP H''.
  case: rl Harl H'=>/=.
  - by move=>_; rewrite maxn0 H'' -{1}(addn0 (height _)) eqn_add2l.
  move=>lrl krl vrl brl rrl=>/= /and3P [Hlrl -> ->].
  case: brl Hlrl=>/=.
  - move/eqP->; rewrite maxn_addl H''.
    case: (ltngtP (height r) (height rrl + 1 + 1))=>_;
      try by rewrite -{1}(addn0 (height _)) eqn_add2l.
    by rewrite eqn_add2r=>/eqP<-; rewrite maxn_addr !maxnn !eq_refl Hall Hr.
  - move/eqP->; rewrite maxnn H''.
    case: (ltngtP (height r) (height lrl + 1))=>_;
      try by rewrite -{1}(addn0 (height _)) eqn_add2l.
    by rewrite eqn_add2r=>/eqP->; rewrite !maxnn !eq_refl Hall Hr.
  move/eqP->; rewrite maxn_addr H''.
  case: (ltngtP (height r) (height lrl + 1 + 1))=>_;
    try by rewrite -{1}(addn0 (height _)) eqn_add2l.
  by rewrite eqn_add2r=>/eqP<-; rewrite maxn_addl !maxnn !eq_refl Hall Hr.
- by move/eqP <-; rewrite maxn_addl maxnn addn0 !eq_refl Hl Hr.
by rewrite eqn_add2r=>/eqP->; rewrite maxn_addr maxnn !eq_refl Hl Hr.
Qed.

Lemma avl_split_max (l : kvtree K V) k v b r t k' v' :
  split_max l k v b r = (t, k', v') ->
  bal_inv (height l) b (height r) -> avl l -> avl r ->
  avl t && (maxn (height l) (height r) + 1 == height t + decr (Node l k v b r) t).
Proof.
elim: r=>/= [|lr _ kr vr br rr IHr] in l k v b t *.
- case=><- _ _; rewrite maxn0 => H /[dup] E -> _ /=.
  case: b H=>/=; rewrite /decr /=.
  - rewrite add0n=>/[dup] H /eqP ->; rewrite eqn_add2l eq_sym eqb1.
    case: l E H=>//= l zk zv b r.
    rewrite -{2}(add0n 1%N) eqn_add2r; case: b=>//=; case/and3P=>/eqP->_ _.
    - by rewrite maxn_addl addn1=>/eqP.
    by rewrite maxn_addr addn1=>/eqP.
  - by rewrite eq_sym=>/heightE->.
  by rewrite addn1=>/eqP.
case Hsm: (split_max lr kr vr br rr)=>[[r' kr'] vr']; case=><- Ek Ev;
  rewrite {kr'}Ek {vr'}Ev in Hsm.
move=>H Hl /and3P [Hbr Hlr Hrr].
case/andP: (IHr _ _ _ _ _ Hsm Hbr Hlr Hrr)=>Har' Hh.
case: ifP=>/= Hd; rewrite Hd /= in Hh.
- rewrite /bal_inv /= in H; rewrite (eqP Hh) in H *.
  by apply: avl_balL_decr.
by case: b H=>/=; rewrite (eqP Hh) addn0=>/eqP->; rewrite addn0 !eq_refl Hl Har'.
Qed.

Lemma avl_delete_b k t :
  avl t ->
  avl (delete k t) && (height t == height (delete k t) + decr t (delete k t)).
Proof.
elim/avl_ind=>//=l k0 v0 b r E Hl Hr /andP [Hal Hhl] /andP [Har Hhr].
case: (cmp k k0)=>/=.
- (* k < k0 *)
  case: ifP=>/=; last first.
  - by move=>Hi; case: b E=>/=; move/eqP: Hhl=>->;
    rewrite Hi !addn0=>/eqP->; rewrite Hal Hr !eq_refl.
  (* decr l delete *)
  move=>Hi; rewrite Hi /= in Hhl; case: b E=>E /=.
  - (* b = Lh *)
    rewrite Hal Hr; move: Hhl; rewrite (eqP E) eqn_add2r=>/eqP<-.
    by rewrite maxnn maxn_addl !eq_refl.
  - (* b = Bal *)
    rewrite Hal Hr; move: Hhl; rewrite (eqP E) maxnn =>/eqP->.
    by rewrite maxn_addr addn0 !eq_refl.
  (* b = Rh *)
  case: {Har Hhr}r Hr E=>/=; first by rewrite addn1.
  move=>lr kr vr br rr /=; case/and3P; case: br=>/=.
  - case: lr=>/=; first by rewrite addn1=>/eqP.
    move=>llr klr vlr blr rlr /=; rewrite eqn_add2r=>Hrr; case: blr=>/=.
    - rewrite -(eqP Hrr); case/and3P =>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
      rewrite !maxn_addl !eqn_add2r=>/eqP <-.
      by rewrite !maxn_addr !maxnn !eq_refl Hal Hallr Harlr Harr.
    - rewrite -(eqP Hrr); case/and3P=>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
      rewrite maxn_addl !maxnn !eqn_add2r=>/eqP <-.
      by rewrite maxn_addr !maxnn !eq_refl Hal Hallr Harlr Harr.
    rewrite -(eqP Hrr); case/and3P =>/eqP-> Hallr Harlr Harr; move/eqP: Hhl=>->.
    rewrite !maxn_addl !maxn_addr !eqn_add2r=>/eqP <-.
    by rewrite !maxn_addr !maxn_addl !maxnn !eq_refl Hal Hallr Harlr Harr.
  - move/eqP=>-> Halr Harr; rewrite (eqP Hhl) maxnn !eqn_add2r =>/eqP->.
    by rewrite !maxn_addr maxn_addl addn0 !eq_refl Hal Halr Harr.
  move/eqP=>-> Halr Harr; rewrite (eqP Hhl) maxn_addr !eqn_add2r =>/eqP <-.
  by rewrite !maxnn maxn_addr !eq_refl Hal Halr Harr.
- (* k == k0 *)
  case: {Hal Hhl} l Hl E=>/=.
  - move=>_; case: b=>/=; rewrite /decr /=.
    - by rewrite addn1 => /eqP.
    - by move/heightE=>->.
    rewrite add0n max0n Hr => H /=; rewrite eqn_add2l.
    case: {Har Hhr}r Hr H=>//=lr kr vr br rr /=.
    rewrite -{2}(add0n 1%N) eqn_add2r; case: br=>//=; case/and3P=>/eqP=>->_ _.
    - by rewrite maxn_addl addn1=>/eqP.
    by rewrite maxn_addr addn1=>/eqP.
  move=>ll kl vl bl rl=>/and3P [Hb Hall Harl] Hbl.
  case Hsm: (split_max ll kl vl bl rl)=>[[l' k'] v'].
  case/andP: (avl_split_max Hsm Hb Hall Harl)=>Hal'; case: ifP=>/= Hd.
  - rewrite eqn_add2r => /eqP E'; move: Hbl; rewrite E'; case: b=>/=.
    - by rewrite eqn_add2r=>/eqP->; rewrite maxn_addl maxnn !eq_refl Hal' Hr.
    - by move/eqP=>->; rewrite maxn_addr maxnn addn0 !eq_refl Hal' Hr.
    case: {Har Hhr}r Hr=>/=; first by rewrite addn1=>/eqP.
    move=>lr kr vr br rr; rewrite eqn_add2r=>/and3P [H'' Halr Harr] E''.
    case: br H'' =>/=.
    - case: lr Halr E''=>/=; first by move=>_ _; rewrite addn1=>/eqP.
      move=>llr klr vlr blr rlr; case: blr=>/= /and3P [/eqP-> Hallr Harlr].
      - rewrite maxn_addl !eqn_add2r=>/[swap]/eqP<-.
        rewrite maxn_addl eqn_add2r=>/eqP<-.
        by rewrite !maxn_addr !maxnn !eq_refl Hal' Hallr Harlr Harr.
      - rewrite maxnn !eqn_add2r=>/[swap]/eqP->.
        rewrite maxn_addl maxnn eqn_add2r=>/eqP->.
        by rewrite !maxnn maxn_addr !eq_refl Hal' Hallr Harlr Harr.
      rewrite maxn_addr !eqn_add2r=>/[swap]/eqP<-.
      rewrite maxn_addl eqn_add2r=>/eqP<-.
      by rewrite maxn_addl maxn_addr !maxnn !eq_refl Hal' Hallr Harlr Harr.
    - move: E''=>/[swap]/eqP->; rewrite maxnn=>/eqP->.
      by rewrite !maxn_addr maxn_addl addn0 !eq_refl Hal' Halr Harr.
    move: E''=>/[swap]/eqP->; rewrite maxn_addr !eqn_add2r=>/eqP->.
    by rewrite !maxnn maxn_addr !eq_refl Hal' Halr Harr.
  by rewrite addn0 Hal' Hr; move: Hbl=>/[swap]/eqP->-> /=; case: b=>/=; rewrite addn0.
(* k > k0 *)
case: ifP=>/=; last first.
- by move=>Hi; case: b E=>/=; move/eqP: Hhr=>->;
  rewrite Hi !addn0=>/eqP->; rewrite Har Hl !eq_refl.
(* decr l delete *)
move=>Hi; rewrite Hi /= in Hhr; case: b E=>E /=.
- (* b = Lh *)
  case: {Hal Hhl}l Hl E=>/=; first by rewrite addn1.
  move=>ll kl vl bl rl /=; case/and3P; case: bl=>/=.
  - move/eqP=>-> Hall Harl; rewrite (eqP Hhr) maxn_addl !eqn_add2r =>/eqP <-.
    by rewrite !maxnn maxn_addl !eq_refl Har Hall Harl.
  - move/eqP=>-> Hall Harl; rewrite (eqP Hhr) maxnn !eqn_add2r =>/eqP->.
    by rewrite !maxn_addl maxn_addr addn0 !eq_refl Har Hall Harl.
  case: rl=>/=; first by rewrite addn1=>/eqP.
  move=>lrl krl vrl brl rrl /=; rewrite eqn_add2r=>Hll Hall; case: brl=>/=.
  - rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
    rewrite maxn_addl maxn_addr !eqn_add2r; move/eqP: Hhr=>->.
    rewrite !eqn_add2r =>/eqP <-.
    by rewrite !maxn_addr maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
  - rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
    rewrite maxnn maxn_addr !eqn_add2r; move/eqP: Hhr=>->.
    rewrite !eqn_add2r =>/eqP <-.
    by rewrite maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
  rewrite -(eqP Hll); case/and3P=>/eqP-> Halrl Harrl.
  rewrite !maxn_addr maxn_addl !eqn_add2r; move/eqP: Hhr=>->.
  rewrite !eqn_add2r =>/eqP <-.
  by rewrite maxn_addl !maxnn !eq_refl Hall Halrl Harrl Har.
- (* b = Bal *)
  rewrite Har Hl; move: Hhr; rewrite (eqP E) maxnn =>/eqP->.
  by rewrite maxn_addl addn0 !eq_refl.
(* b = Rh *)
rewrite Har Hl; move: Hhr; rewrite (eqP E) eqn_add2r=>/eqP<-.
by rewrite maxnn maxn_addr !eq_refl.
Qed.

(* correctness via sorted lists *)

Fixpoint inorder_kv (t : kvtree K V) : seq (K*V) :=
  if t is Node l k v _ r
    then inorder_kv l ++ [:: (k,v)] ++ inorder_kv r
  else [::].

Lemma inorder_rot2 (l : kvtree K V) ak av m bk bv r :
  inorder_kv (rot2 l ak av m bk bv r) =
  inorder_kv l ++ (ak,av) :: inorder_kv m ++ (bk,bv) :: inorder_kv r.
Proof.
rewrite /rot2; case: m=>//= ml kl vl bl rl /=.
by rewrite -!catA.
Qed.

Lemma inorder_balL (l : kvtree K V) k v b r :
  inorder_kv (balL l k v b r) = inorder_kv l ++ (k,v) :: inorder_kv r.
Proof.
rewrite /balL; case: b=>//.
case: l=>//= ll kl vl bl lr.
case: bl=>/=; rewrite -catA //.
by apply: inorder_rot2.
Qed.

Lemma inorder_balR (l : kvtree K V) k v b r :
  inorder_kv (balR l k v b r) = inorder_kv l ++ (k,v) :: inorder_kv r.
Proof.
rewrite /balR; case: b=>//.
case: r=>//= rl kr vr br rr.
case: br=>/=; try by rewrite -catA.
by apply: inorder_rot2.
Qed.

Definition kvlist t : bool := sorted <%O (map fst (inorder_kv t)).

Theorem inorder_lookup k t :
  kvlist t ->
  lookup t k = find_list k (inorder_kv t).
Proof.
rewrite /kvlist; elim: t=>//=l IHl k0 v0 b r IHr H.
rewrite findlist_sorted_cat_cons_cat //=.
move: H; rewrite map_cat /= sorted_cat_cons_cat=>/andP /= [H1 H2].
case: cmpE=>// Hk.
- by apply: IHr; move/path_sorted: H2.
by apply: IHl; rewrite (cat_sorted2 H1).
Qed.

Theorem inorder_upsert k v t :
  kvlist t ->
  inorder_kv (upsert k v t) = ins_list k v (inorder_kv t).
Proof.
rewrite /kvlist; elim: t=>//=l IHl k0 v0 b r IHr.
rewrite !map_cat /= sorted_cat_cons_cat=>/andP [H1 H2].
rewrite inslist_sorted_cat_cons_cat; last by rewrite map_cat.
case: cmpE=>Hx /=.
- case: cmpE Hx=>// _ _; rewrite -cat1s in H2.
  by case: ifP=>/=_; rewrite ?inorder_balR /= IHr // (cat_sorted2 H2).
- by rewrite Hx cmpxx /=.
by case: ifP=>/=_; rewrite ?inorder_balL /= IHl // (cat_sorted2 H1).
Qed.

Lemma inorder_split_max (l : kvtree K V) k v b r t k' v' :
  split_max l k v b r = (t, k', v') ->
  inorder_kv t ++ [:: (k',v')] = inorder_kv l ++ (k,v) :: inorder_kv r.
Proof.
elim: r l k v b t =>/= [|lr _ kr vr br rr IHr] l k v b t; first by case=>->->->.
case Hsm: (split_max lr kr vr br rr)=>[[r' k0] v0][<- Hk Hv] /=; rewrite {k0}Hk {v0}Hv in Hsm.
by case: ifP=>/= _; rewrite ?inorder_balL /= -(IHr _ _ _ _ _ Hsm) -catA.
Qed.

Theorem inorder_delete k t :
  kvlist t ->
  inorder_kv (delete k t) = del_list k (inorder_kv t).
Proof.
rewrite /kvlist /=; elim: t=>//=l IHl k0 v0 c r IHr /[dup] H.
rewrite map_cat /= sorted_cat_cons_cat=>/andP [H1 H2].
rewrite dellist_sorted_cat_cons_cat //.
case: cmpE=>Hxa /=.
- case: ltgtP Hxa=>//_ _; rewrite -cat1s in H2.
  by case: ifP=>/=_; rewrite ?inorder_balL IHr // (cat_sorted2 H2).
- rewrite Hxa eqxx.
  case: {H H1 IHl}l=>//= ll kl vl bl rl.
  case Hsm: (split_max ll kl vl bl rl)=>[[a' rk'] rv'] /=.
  move: (inorder_split_max Hsm)=>/= Esm.
  by case: ifP=>/=_; rewrite ?inorder_balR -Esm -catA.
by case: ifP=>/=_; rewrite ?inorder_balR IHl // (cat_sorted2 H1).
Qed.

Definition invariant (t : kvtree K V) := kvlist t && avl t.

Theorem invariant_empty : invariant leaf.
Proof. by []. Qed.

Theorem lookup_empty : lookup leaf =1 fun => None.
Proof. by []. Qed.

Corollary invariant_upsert k v t :
  invariant t -> invariant (upsert k v t).
Proof.
rewrite /invariant /kvlist => /andP [H1 H2].
apply/andP; split; last by case/andP: (avl_upsert k v H2).
by rewrite inorder_upsert //; apply: ins_list_sorted.
Qed.

Corollary lookup_upsert k v t :
  invariant t ->
  lookup (upsert k v t) =1 [eta lookup t with k |-> Some v].
Proof.
move/[dup] => H; rewrite /invariant /kvlist => /andP [H1 _].
move=>x /=; rewrite inorder_lookup; last by case/(invariant_upsert k v)/andP: H.
rewrite inorder_upsert //; case: (eqVneq x k)=>[->|N].
- by rewrite find_ins_list_same.
by rewrite find_ins_list_diff // inorder_lookup.
Qed.

Definition AVLMap :=
  @Map.make _ _ (kvtree K V) leaf upsert delete lookup
  invariant
  invariant_empty lookup_empty
  invariant_upsert lookup_upsert
  (* invariant_delete lookup_delete *)
  .

End AVLMap.

(*
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Extract Inductive reflect => bool [ true false ].

Extraction "avl_ext.ml" bintree_full.leaf insert_b delete_b isin_a.
*)
