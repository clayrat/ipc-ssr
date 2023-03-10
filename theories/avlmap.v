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
        update : K -> (V -> V) -> V -> tp -> tp * option V;
        delete : K -> tp -> tp * option V;
        lookup : tp -> K -> option V;

        invar : tp -> bool;

        _ : invar empty;
        _ : lookup empty =1 fun => None;

        _ : forall k f v s, invar s -> invar (update k f v s).1;
        _ : forall k f v s, invar s ->
            let tv := update k f v s in
            (lookup tv.1 =1 [eta (lookup s) with k |->
                              oapp (Some \o f) (Some v) (lookup s k)])
            *
            (tv.2 = lookup s k);

        _ : forall k s, invar s -> invar (delete k s).1;
        _ : forall k s, invar s ->
            let tv := delete k s in
            (lookup tv.1 =1 [eta (lookup s) with k |-> None])
            *
            (tv.2 = lookup s k)
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

Fixpoint find_list (xs : seq (K*V)) (k : K) : option V :=
  if xs is (k0,v)::xs' then
    match cmp k k0 with
    | LT => None
    | EQ => Some v
    | GT => find_list xs' k
    end
  else None.

Fixpoint ins_list (k : K) (f : V -> V) (v : V) (xs : seq (K*V)) : seq (K*V) * option V :=
  if xs is (k0,v0)::xs' then
    match cmp k k0 with
    | LT => ((k,v) :: (k0,v0) :: xs', None)
    | EQ => ((k,f v0) :: xs', Some v0)
    | GT => let '(xs1, ov) := ins_list k f v xs' in
            ((k0,v0) :: xs1, ov)
    end
  else ([::(k,v)], None).

Fixpoint del_list (k : K) (xs : seq (K*V)) : seq (K*V) * option V :=
  if xs is (k0,v0) :: xs' then
    match cmp k k0 with
    | LT => ((k0,v0) :: xs', None)
    | EQ => (xs', Some v0)
    | GT => let '(xs1, ov) := del_list k xs' in
            ((k0,v0) :: xs1, ov)
    end
  else ([::], None).

Definition keys : seq (K*V) -> seq K := map fst.
Definition values : seq (K*V) -> seq V := map snd.

Lemma findlist_empty : find_list [::] =1 (fun=> None).
Proof. by []. Qed.

Lemma findlist_path k xs : path <%O k (keys xs) -> find_list xs k = None.
Proof.
rewrite /keys; case: xs=>//=; case=>k0 v0 xs /=; case/andP=>H1 _.
by case: cmpE H1.
Qed.

Lemma findlist_sorted_cat_cons_cat (xs ys : seq (K*V)) k k' v' :
  sorted <%O (keys (xs ++ (k',v') :: ys)) ->
  find_list (xs ++ (k',v') :: ys) k = if k < k'
                                       then find_list xs k
                                       else find_list ((k',v') :: ys) k.
Proof.
rewrite /keys; elim: xs=>/=; first by move=>H; case: cmpE.
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

Lemma inorder_ins_list k f v xs :
  sorted <%O (keys xs) ->
  perm_eq (keys (ins_list k f v xs).1)
          (if k \in keys xs then keys xs else k :: keys xs).
Proof.
elim: xs=>//=[[k0 v0]] xs IH /= Hp.
case E: (ins_list k f v xs)=>[xs1 ov]; rewrite E /= in IH.
rewrite inE; case: cmpE=>/= Hk.
- move/path_sorted: Hp=>/IH; case: ifP=>H; first by rewrite perm_cons.
  by move=>H1; rewrite perm_sym -cat1s -(cat1s k0) perm_catCA /= perm_cons perm_sym.
- by rewrite Hk.
case: ifP=>//; move: (order_path_min lt_trans Hp)=>/allP/[apply].
by rewrite ltNge le_eqVlt Hk orbT.
Qed.

Lemma inslist_sorted_cat_cons_cat (xs ys : seq (K*V)) k f v k' v' :
  sorted <%O (keys (xs ++ [::(k',v')])) ->
  ins_list k f v (xs ++ (k',v') :: ys) =
    if k < k'
      then
        let '(xs1, ov) := ins_list k f v xs in
        (xs1 ++ (k',v') :: ys, ov)
      else
        let '(ys1, ov) := ins_list k f v ((k',v') :: ys) in
        (xs ++ ys1, ov).
Proof.
rewrite /keys; elim: xs=>/=.
- move=>_; case: (cmpE k k')=>// Hk.
  by case: (ins_list k f v ys).
move=>[k0 v0] /= xs + H; rewrite map_cat /= in H.
move: (H); move/(order_path_min lt_trans).
rewrite map_cat all_cat /= andbT =>/andP [Hxs Hya].
case: (cmpE k k')=>H'.
- case E: (ins_list k f v (xs ++ (k', v') :: ys))=>[xs1 ov] /=.
  case E0: (ins_list k f v xs)=>[xs0 ov0] /=.
  case: (cmpE k k0)=>//= H0.
  by move/path_sorted: H=>/[swap]/[apply]; case=>->->.
- case E: (ins_list k' f v (xs ++ (k', v') :: ys))=>[xs1 ov] /=.
  rewrite {k}H'; case: (cmpE k' k0) Hya=>// Hya _ -> //.
  by apply: (path_sorted H).
case E: (ins_list k f v (xs ++ (k', v') :: ys))=>[ys1 ov] /=.
case E0: (ins_list k f v ys)=>[ys0 ov0] /=.
case: (cmpE k k0) (lt_trans Hya H')=>// H0 _.
by move/path_sorted: H=>/[swap]/[apply]; case=>->->.
Qed.

Lemma del_nop k xs :
  path <%O k (keys xs) -> del_list k xs = (xs, None).
Proof.
elim: xs=>//= [[k0 v0]] xs IH /= /andP [H1 H2].
by case: cmpE H1.
Qed.

Lemma inorder_del_list k xs :
  sorted <%O (keys xs) ->
  perm_eq (keys (del_list k xs).1)
          (filter (predC1 k) (keys xs)).
Proof.
rewrite /keys; elim: xs=>// [[k0 v0]] /= xs IH Hp.
move/path_sorted: (Hp)=>/IH /= {IH}H.
case Ed: (del_list k xs)=>[xs1 ov]; rewrite Ed /= in H.
case: cmpE=>/=.
- move=>Hk; rewrite perm_cons.
  suff : all (predC1 k) (keys xs) by move/all_filterP->.
  apply (sub_all (a1:=> k)).
  - by move=>z /=; rewrite lt_neqAle eq_sym; case/andP.
  by apply/(path_all lt_trans)/(path_le lt_trans)/Hp.
- move=>E; rewrite -{k0}E in Hp.
  suff : all (predC1 k) (keys xs) by move/all_filterP->.
  apply (sub_all (a1:=> k)).
  - by move=>z /=; rewrite lt_neqAle eq_sym; case/andP.
  by apply/(path_all lt_trans).
by move=>Hk; rewrite perm_cons.
Qed.

Lemma dellist_sorted_cat_cons_cat (xs ys : seq (K*V)) k k' v' :
  sorted <%O (keys (xs ++ (k',v') :: ys)) ->
  del_list k (xs ++ (k',v') :: ys) =
    if k < k'
      then
        let '(xs1, ov) := del_list k xs in
        (xs1 ++ (k',v') :: ys, ov)
      else
        let '(ys1, ov) := del_list k ((k',v') :: ys) in
        (xs ++ ys1, ov).
Proof.
rewrite /keys; elim: xs=>/=.
- move=>H; case: cmpE=>// Hk.
  by case E: (del_list k ys).
case=>k0 v0 xs /= + H; rewrite map_cat /= in H.
move: (H); move/(order_path_min lt_trans).
rewrite map_cat all_cat /= =>/and3P [Hxs Hya Hys].
case: (cmpE k k')=>H'.
- case E: (del_list k (xs ++ (k', v') :: ys))=>[xs1 ov] /=.
  case E0: (del_list k xs)=>[xs0 ov0] /=.
  case: (cmpE k k0)=>//= H0.
  by move/path_sorted: H=>/[swap]/[apply]; case=>->->.
- case E: (del_list k' (xs ++ (k', v') :: ys))=>[xs1 ov] /=.
  rewrite {k}H'; case: (cmpE k' k0) Hya=>// Hya _ -> //.
  by apply: (path_sorted H).
case E: (del_list k (xs ++ (k', v') :: ys))=>[ys1 ov] /=.
case E0: (del_list k ys)=>[ys0 ov0] /=.
case: (cmpE k k0) (lt_trans Hya H')=>// H0 _.
by move/path_sorted: H=>/[swap]/[apply]; case=>->->.
Qed.

Definition kvlist xs := sorted <%O (keys xs) && uniq (keys xs).

Lemma del_list_keys k xs :
  kvlist xs ->
  subseq (keys (del_list k xs).1) (keys xs).
Proof.
rewrite /kvlist; elim: xs=>// [[k0 v0]] /= xs IH.
case/and3P=>Hp N U.
case E0: (del_list k xs)=>[xs0 ov0] /=; rewrite E0 /= in IH.
move/path_sorted: (Hp)=>Hs; rewrite Hs U in IH; move: (IH erefl)=>{}IH.
case: cmpE=>/= Hk.
- by rewrite eqxx.
- rewrite {k0}Hk in Hp N *.
  case Exs: (keys xs) IH=>[|kx kxs] //; case: eqP=>[E|] //.
  by move: N; rewrite -E Exs inE eqxx.
by rewrite eqxx.
Qed.

Lemma kvlist_empty : kvlist [::].
Proof. by []. Qed.

Lemma kvlist_ins_list k f v xs :
  kvlist xs -> kvlist (ins_list k f v xs).1.
Proof.
rewrite /kvlist; case/andP; elim: xs=>//=[[k0 v0]] xs /= IH Hp /andP [N0 U].
case: cmpE=>Hk /=; first last.
- rewrite inE negb_or -!andbA; apply/and6P; split=>//; first by case: ltgtP Hk.
  by apply: (path_notin lt_trans)=>//; apply/(path_le lt_trans)/Hp.
- by rewrite -Hk Hp N0.
case E0: (ins_list k f v xs)=>[xs0 ov0] /=; rewrite E0 /= in IH.
move: Hp; rewrite !(path_sortedE lt_trans) -andbA.
case/andP=>H1 H2; case/andP: (IH H2 U)=>->-> /=; rewrite andbT.
have Hi := inorder_ins_list k f v H2; rewrite E0 /= in Hi.
apply/andP; split.
- by rewrite (perm_all _ Hi); case: ifP=>//= _; rewrite Hk.
rewrite (perm_mem Hi); case: ifP=>// _.
rewrite inE negb_or N0 andbT.
by case: ltgtP Hk.
Qed.

Lemma find_ins_list k f v xs :
  let sv := ins_list k f v xs in
  (find_list sv.1 =1 [eta (find_list xs) with k |->
                      oapp (Some \o f) (Some v) (find_list xs k)])
  * (sv.2 = find_list xs k).
Proof.
move; elim: xs=>/=; first by split=>// q /=; case: cmpE.
case=>k0 v0 xs.
case E0: (ins_list k f v xs)=>[xs0 ov0] /=.
case=>IH1 IH2; case: (cmpE k k0)=>Hk /=; split=>// q /=.
- by case: cmpE=>// Hq; case: cmpE (lt_trans Hq Hk).
- by rewrite Hk; case: cmpE.
case: (cmpE q k0)=>Hq0.
- by move: (lt_trans Hq0 Hk); rewrite lt_neqAle; case/andP=>/negbTE->.
by rewrite Hq0; move: Hk; rewrite lt_neqAle; case/andP=>/negbTE->.
by apply: IH1.
Qed.

Lemma kvlist_del_list k xs :
  kvlist xs -> kvlist (del_list k xs).1.
Proof.
rewrite /kvlist; case/andP.
elim: xs=>// [[k0 v0]] xs /=.
case E0: (del_list k xs)=>[xs0 ov0] /= IH /= Hp /andP [N0 U].
move/path_sorted: (Hp)=>H1; case/andP: (IH H1 U)=>{IH}H2 {}U1.
have S: subseq (keys xs0) (keys xs).
- by move: (@del_list_keys k xs); rewrite E0 /=; apply; apply/andP.
case: cmpE=>/= Hk; first last.
- by apply/and3P.
- by apply/andP.
apply/and3P; split=>//.
- by apply/(subseq_path lt_trans)/Hp.
by apply: contra N0; move/mem_subseq: S; apply.
Qed.

Lemma find_del_list k xs :
  kvlist xs ->
  let sv := del_list k xs in
  (find_list sv.1 =1 [eta find_list xs with k |-> None])
  * (sv.2 = find_list xs k).
Proof.
rewrite /kvlist /=; case/andP.
elim: xs=>//; first by move=>_ _; split=>// q /=; rewrite if_same.
case=>k0 v0 xs.
case E0: (del_list k xs)=>[xs0 ov0] /= IH /= /[dup] H /path_sorted H' /andP [N0 U].
move: (IH H' U)=>{IH}[IH1 IH2].
rewrite E0; case: (cmpE k k0)=>/= Hk; split=>// q /=.
- by case: eqP=>// ->; case: cmpE Hk.
- rewrite -Hk; case: cmpE=>//.
  - by move=><-; apply: findlist_path; rewrite Hk.
  move=>Hq; apply/findlist_path/(path_le lt_trans)/H.
  by rewrite -Hk.
move: (IH1 q)=>/= {}IH1.
case: cmpE=>// Hq.
- case: cmpE (lt_trans Hk Hq)=>// _ _; rewrite IH1.
  by move: Hq; rewrite lt_neqAle eq_sym; case/andP=>/negbTE->.
- rewrite -Hq in IH1 *; case: cmpE Hk=>// _ _.
  by rewrite IH1 eqxx.
case: cmpE=>// Hq0; rewrite IH1.
by move: Hq; rewrite lt_neqAle eq_sym; case/andP=>/negbTE->.
Qed.

Definition KVLMap :=
  Map.make kvlist_empty findlist_empty
           kvlist_ins_list (fun k f v s _ => find_ins_list k f v s)
           kvlist_del_list find_del_list.

End KVList.

Section KVListEqSeq.
Context {disp : unit} {K : orderType disp} {V : eqType}.

Lemma perm_flatten_values_cons k v (xs : seq (K * seq V)) :
  sorted <%O (keys xs) ->
  perm_eq (flatten (values (ins_list k (cons v) [::v] xs).1))
          (v :: flatten (values xs)).
Proof.
elim: xs=>//=[[k0 v0]] xs.
case E0: (ins_list k (cons v) [:: v] xs)=>[xs0 ov0] /= IH /= Hp.
case: cmpE=>Hk //=.
move/path_sorted: Hp=>/IH H1.
by rewrite perm_sym -cat1s perm_catCA /= perm_sym (perm_catl _ H1).
Qed.

Lemma perm_flatten_lookup_del k (xs : seq (K * seq V)) :
  sorted <%O (keys xs) ->
  perm_eq (flatten (values xs))
          (odflt [::] (find_list xs k) ++ flatten (values (del_list k xs).1)).
Proof.
elim: xs=>//=[[k0 v0]] xs.
case E0: (del_list k xs)=>[xs0 ov0] /= IH /= Hp.
case: cmpE=>Hk //=.
move/path_sorted: Hp=>/IH H1.
by rewrite perm_sym perm_catCA /= perm_sym (perm_catl _ H1).
Qed.

End KVListEqSeq.

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

Lemma incr_refl t : incr t t = ~~ is_node t.
Proof. by rewrite /incr andbN orbF. Qed.

(* leaf cases are essentially placeholders for totality *)

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

Definition balL (ab : kvtree K V) (zk : K) (zv : V) (bb : bal) (c : kvtree K V) : kvtree K V :=
  match bb with
  | Lh  => match ab with
           | Node a xk xv Lh  b => Node a xk xv Bal (Node b zk zv Bal c)
           | Node a xk xv Bal b => Node a xk xv Rh  (Node b zk zv Lh  c)
           | Node a xk xv Rh  b => rot2 a xk xv b           zk zv c
           | Leaf               => Node leaf zk zv Bal c
           end
  | Bal => Node ab zk zv Lh  c
  | Rh  => Node ab zk zv Bal c
  end.

Definition balR (a : kvtree K V) (xk : K) (xv : V) (bb : bal) (bc : kvtree K V) : kvtree K V :=
  match bb with
  | Lh  => Node a xk xv Bal bc
  | Bal => Node a xk xv Rh  bc
  | Rh  => match bc with
           | Node b zk zv Lh  c => rot2 a xk xv b zk zv c
           | Node b zk zv Bal c => Node (Node a xk xv Rh  b) zk zv Lh  c
           | Node b zk zv Rh  c => Node (Node a xk xv Bal b) zk zv Bal c
           | Leaf               => Node a xk xv Bal leaf
           end
  end.

Fixpoint lookup (t : kvtree K V) (k : K) : option V :=
  if t is Node l k0 v0 _ r
    then match cmp k k0 with
           | LT => lookup l k
           | EQ => Some v0
           | GT => lookup r k
         end
  else None.

Lemma lookup_node t k : lookup t k -> is_node t.
Proof. by case: t. Qed.

Fixpoint upsert (k : K) (f : V -> V) (v : V) (t : kvtree K V) : kvtree K V * option V :=
  if t is Node l k0 v0 b r
    then match cmp k k0 with
         | LT => let '(l', ov) := upsert k f v l in
                 (if incr l l' then balL l' k0 v0 b r else Node l' k0 v0 b r, ov)
         | EQ => (Node l k (f v0) b r, Some v0)
         | GT => let '(r', ov) := upsert k f v r in
                 (if incr r r' then balR l k0 v0 b r' else Node l k0 v0 b r', ov)
         end
    else (Node leaf k v Bal leaf, None).

Lemma avl_upsert k f v t :
  avl t ->
  avl (upsert k f v t).1 &&
    (height (upsert k f v t).1 == height t + incr t (upsert k f v t).1).
Proof.
elim/avl_ind=>//= l k0 v0 b r E Hl Hr.
case El: (upsert k f v l)=>[l0 ovl] /=.
case Er: (upsert k f v r)=>[r0 ovr] /=.
move=>/andP [Hal Hhl] /andP [Har Hhr].
case: (cmp k k0)=>/=.
- (* k < k0 *)
  case: ifP=>/= Hi; last first.
  - case: b E=>/=; move/eqP: Hhl=>->/eqP->;
    by rewrite Hi !addn0 Hal Hr !eq_refl.
  (* incr l insert *)
  rewrite Hi /= in Hhl.
  case: b E=>/eqP E /=.
  - (* b = Lh *)
    case E': l0 Hi => [|li ki vi bi ri]/=.
    - (* insert = Leaf, impossible *)
      by rewrite E' addn1 in Hhl.
    (* insert = Node *)
    move: Hal Hhl; rewrite {}E' E /= maxn_addl addn0; case: bi=>/=.
    - (* bi = Lh *)
      case/and3P=>/eqP->->->/=.
      by rewrite maxn_addl !eqn_add2r=>/eqP<-; rewrite !maxnn Hr !eqxx.
    - (* bi = Bal *)
      case: {El Hl}l E; rewrite /incr /=; first by rewrite addn1.
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
case E': r0=> [|li ki vi bi ri]/=.
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
  case: {Er Hr}r E; rewrite /incr /=; first by rewrite addn1.
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

Fixpoint delete (k : K) (t : kvtree K V) : kvtree K V * option V :=
  if t is Node l k0 v0 ba r
    then match cmp k k0 with
         | LT => let '(l',ov) := delete k l in
                 (if decr l l' then balR l' k0 v0 ba r else Node l' k0 v0 ba r, ov)
         | EQ => (if l is Node ll kl vl bl rl then
                   let: (l', k', v') := split_max ll kl vl bl rl in
                   if decr l l' then balR l' k' v' ba r
                                else Node l' k' v' ba r
                   else r, Some v0)
         | GT => let '(r',ov) := delete k r in
                 (if decr r r' then balL l k0 v0 ba r' else Node l k0 v0 ba r', ov)
         end
    else (leaf, None).

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

Lemma avl_delete k t :
  avl t ->
  avl (delete k t).1 &&
    (height t == height (delete k t).1 + decr t (delete k t).1).
Proof.
elim/avl_ind=>//=l k0 v0 b r E Hl Hr.
case El: (delete k l)=>[l0 ovl] /=.
case Er: (delete k r)=>[r0 ovr] /=.
move=>/andP [Hal Hhl] /andP [Har Hhr].
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
  case: {Er Har Hhr}r Hr E=>/=; first by rewrite addn1.
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
  case: {El Hal Hhl} l Hl E=>/=.
  - move=>_; case: b=>/=; rewrite /decr /=.
    - by rewrite addn1 => /eqP.
    - by move/heightE=>->.
    rewrite add0n max0n Hr => H /=; rewrite eqn_add2l.
    case: {Er Har Hhr}r Hr H=>//=lr kr vr br rr /=.
    rewrite -{2}(add0n 1%N) eqn_add2r; case: br=>//=; case/and3P=>/eqP=>->_ _.
    - by rewrite maxn_addl addn1=>/eqP.
    by rewrite maxn_addr addn1=>/eqP.
  move=>ll kl vl bl rl=>/and3P [Hb Hall Harl] Hbl.
  case Hsm: (split_max ll kl vl bl rl)=>[[l' k'] v'].
  case/andP: (avl_split_max Hsm Hb Hall Harl)=>Hal'; case: ifP=>/= Hd.
  - rewrite eqn_add2r => /eqP E'; move: Hbl; rewrite E'; case: b=>/=.
    - by rewrite eqn_add2r=>/eqP->; rewrite maxn_addl maxnn !eq_refl Hal' Hr.
    - by move/eqP=>->; rewrite maxn_addr maxnn addn0 !eq_refl Hal' Hr.
    case: {Er Har Hhr}r Hr=>/=; first by rewrite addn1=>/eqP.
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
  case: {El Hal Hhl}l Hl E=>/=; first by rewrite addn1.
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

Fixpoint inorder_kv (t : kvtree K V) : seq (K*V) :=
  if t is Node l k v _ r
    then inorder_kv l ++ (k,v) :: inorder_kv r
  else [::].

(* correctness via sorted lists *)

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

Definition kv_inorder t : bool := kvlist (inorder_kv t).

Theorem inorder_lookup k t :
  kv_inorder t ->
  lookup t k = find_list (inorder_kv t) k.
Proof.
rewrite /kv_inorder /kvlist /keys; elim: t=>//=l IHl k0 v0 b r IHr /andP [H1 H2].
rewrite findlist_sorted_cat_cons_cat //=.
move: H1 H2; rewrite map_cat /= sorted_cat_cons_cat cat_uniq /=.
case/andP=> /= H1 H2 /and4P [U1 _ _ U2].
case: cmpE=>// Hk.
- by apply: IHr; rewrite (path_sorted H2).
by apply: IHl; rewrite (cat_sorted2 H1).
Qed.

Theorem inorder_upsert k f v t :
  kv_inorder t ->
  (inorder_kv (upsert k f v t).1 = (ins_list k f v (inorder_kv t)).1)
  * ((upsert k f v t).2 = (ins_list k f v (inorder_kv t)).2).
Proof.
rewrite /kv_inorder /kvlist /keys; elim: t=>//= l IHl k0 v0 b r IHr.
case El: (upsert k f v l)=>[l0 ovl] /=; rewrite El /= in IHl.
case Er: (upsert k f v r)=>[r0 ovr] /=; rewrite Er /= in IHr.
rewrite !map_cat /= sorted_cat_cons_cat -andbA => /and3P [H1 H2]; rewrite -cat1s in H2.
rewrite cat_uniq /= =>/and4P [U1 _ _ U2].
rewrite (cat_sorted2 H1) U1 /= in IHl.
case: IHl=>//=>IHl1 IHl2.
rewrite (cat_sorted2 H2) U2 /= in IHr.
case: IHr=>//=>IHr1 IHr2.
rewrite inslist_sorted_cat_cons_cat /keys; last by rewrite map_cat.
case: cmpE=>Hx /=.
- case: cmpE Hx=>// _ _.
  case Er1: (ins_list k f v (inorder_kv r))=>[r1 ovr1] /=.
  by case: ifP=>/=_; rewrite ?inorder_balR /= IHr1 IHr2 Er1.
- by rewrite Hx cmpxx /=.
case El1: (ins_list k f v (inorder_kv l))=>[l1 ovl1] /=.
by case: ifP=>/=_; rewrite ?inorder_balL /= IHl1 IHl2 El1.
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
  kv_inorder t ->
  (inorder_kv (delete k t).1 = (del_list k (inorder_kv t)).1)
  * ((delete k t).2 = (del_list k (inorder_kv t)).2).
Proof.
rewrite /kv_inorder /kvlist /keys /=; elim: t=>//=l IHl k0 v0 c r IHr /andP [] /[dup] H.
case El: (delete k l)=>[l0 ovl] /=; rewrite El /= in IHl.
case Er: (delete k r)=>[r0 ovr] /=; rewrite Er /= in IHr.
rewrite map_cat /= sorted_cat_cons_cat -(cat1s _ (map _ _)) =>/andP [H1 H2].
rewrite cat_uniq /= =>/and4P [U1 _ _ U2].
rewrite (cat_sorted2 H1) U1 /= in IHl.
case: IHl=>//=>IHl1 IHl2.
rewrite (cat_sorted2 H2) U2 /= in IHr.
case: IHr=>//=>IHr1 IHr2.
rewrite dellist_sorted_cat_cons_cat //=.
case: cmpE=>Hxa /=.
- rewrite -cat1s in H2.
  case Er1: (del_list k (inorder_kv r))=>[r1 ovr1] /=.
  by case: ifP=>/=_; rewrite ?inorder_balL IHr1 IHr2 Er1.
- case: {H H1 U1 IHl1 IHl2 El}l=>//= ll kl vl bl rl.
  case Hsm: (split_max ll kl vl bl rl)=>[[a' rk'] rv'] /=.
  move: (inorder_split_max Hsm)=>/= Esm.
  by case: ifP=>/=_; rewrite ?inorder_balR -Esm -catA.
case El1: (del_list k (inorder_kv l))=>[l1 ovl1] /=.
by case: ifP=>/=_; rewrite ?inorder_balR IHl1 IHl2 El1.
Qed.

Definition invariant (t : kvtree K V) := kv_inorder t && avl t.

Theorem invariant_empty : invariant leaf.
Proof. by []. Qed.

Theorem lookup_empty : lookup leaf =1 fun => None.
Proof. by []. Qed.

Corollary invariant_upsert k f v t :
  invariant t -> invariant (upsert k f v t).1.
Proof.
rewrite /invariant /kv_inorder /kvlist => /andP [H1 H2].
case: (inorder_upsert k f v H1)=>-> _.
apply/andP; split; last by case/andP: (avl_upsert k f v H2).
by apply: kvlist_ins_list.
Qed.

Corollary lookup_upsert k f v t :
  invariant t ->
  let tv := upsert k f v t in
  (lookup tv.1 =1 [eta (lookup t) with k |->
                   oapp (Some \o f) (Some v) (lookup t k)])
  * (tv.2 = lookup t k).
Proof.
move/[dup] => H; rewrite /invariant /kvlist => /andP [H1 _].
case E: (upsert k f v t)=>[t0 ov] /=.
move: E; rewrite (surjective_pairing (upsert _ _ _ _)); case=>E1 E2.
case: (find_ins_list k f v (inorder_kv t))=>L1 L2.
case: (inorder_upsert k f v H1)=>I1 I2.
split.
- move=>q /=; rewrite -E1 !inorder_lookup //; last first.
  - by case/(invariant_upsert k f v)/andP: H.
  by rewrite I1 (L1 q) //= -I2 E2.
by rewrite -E2 I2 inorder_lookup.
Qed.

Corollary invariant_delete k t :
  invariant t -> invariant (delete k t).1.
Proof.
rewrite /invariant /kv_inorder /kvlist => /andP [H1 H2].
case: (inorder_delete k H1)=>-> _.
apply/andP; split; last by case/andP: (avl_delete k H2).
by apply: kvlist_del_list.
Qed.

Corollary lookup_delete k t :
  invariant t ->
  let tv := delete k t in
  (lookup tv.1 =1 [eta (lookup t) with k |-> None])
  * (tv.2 = lookup t k).
Proof.
move/[dup] => H; rewrite /invariant /kv_inorder /kvlist => /andP [H1 H2].
case E: (delete k t)=>[t0 ov] /=.
move: E; rewrite (surjective_pairing (delete _ _)); case=>E1 E2.
case: (find_del_list k (xs:=inorder_kv t))=>// L1 L2.
case: (inorder_delete k H1)=>I1 I2.
split.
- move=>x /=; rewrite -E1 !inorder_lookup //; last first.
  - by case/(invariant_delete k)/andP: H.
  by rewrite I1 (L1 x) //= -I2 E2.
by rewrite -E2 I2 inorder_lookup.
Qed.

Definition AVLMap :=
  Map.make invariant_empty lookup_empty
           invariant_upsert lookup_upsert
           invariant_delete lookup_delete.

(* extra operations and properties *)
Fixpoint foldr_v {T} (f : V -> T -> T) (x0 : T) (t : kvtree K V) : T :=
  if t is Node l _ v _ r
    then foldr_v f (f v (foldr_v f x0 r)) l
  else x0.

Lemma foldr_inorder {T} (f : V -> T -> T) x0 t :
  foldr_v f x0 t = foldr (fun kv => f kv.2) x0 (inorder_kv t).
Proof.
elim: t x0=>//= l IHl k v _ r IHr x0.
by rewrite foldr_cat /= -IHr IHl.
Qed.

Lemma upsert_const t k f v :
  (forall x, f x = v) ->
  lookup t k = Some v ->
  (upsert k f v t).1 = t.
Proof.
move=>H; elim: t=>//= l1 IHl k1 v1 b1 r1 IHr.
case El: (upsert k f v l1)=>[l0 ovl] /=.
case Er: (upsert k f v r1)=>[r0 ovr] /=.
case: cmpE=>H1.
- move=>L; move: Er.
  rewrite (surjective_pairing (upsert _ _ _ _)); case=>Er1 _; rewrite Er1 in IHr.
  rewrite (IHr L) incr_refl (@lookup_node _ k) //.
  by apply/optP; exists v.
- by case=>->; rewrite H1 H.
move=>L; move: El.
rewrite (surjective_pairing (upsert _ _ _ _)); case=>El1 _; rewrite El1 in IHl.
rewrite (IHl L) incr_refl (@lookup_node _ k) //.
by apply/optP; exists v.
Qed.

End AVLMap.

Section AVLMapEq.
Context {disp : unit} {K : orderType disp} {V : eqType}.

Fixpoint eqkvtree (t1 t2 : kvtree K V) :=
  match t1, t2 with
  | Leaf, Leaf => true
  | Node l1 k1 v1 b1 r1, Node l2 k2 v2 b2 r2 =>
      [&& k1 == k2, v1 == v2, b1 == b2, eqkvtree l1 l2 & eqkvtree r1 r2 ]
  | _, _ => false
  end.

Lemma eqkvtreeP : Equality.axiom eqkvtree.
Proof.
elim=> [|l1 IHl k1 v1 b1 r1 IHr] [|l2 k2 v2 b2 r2] /=; try by constructor.
have [<-/=|Nk] := k1 =P k2; last by apply: ReflectF; case.
have [<-/=|Nv] := v1 =P v2; last by apply: ReflectF; case.
have [<-/=|Nb] := b1 =P b2; last by apply: ReflectF; case.
apply: (iffP andP).
- by case=>/IHl->/IHr->.
by case=><-<-; split; [apply/IHl|apply/IHr].
Qed.

Canonical kvtree_eqMixin := EqMixin eqkvtreeP.
Canonical kvtree_eqType := Eval hnf in EqType (kvtree K V) kvtree_eqMixin.

End AVLMapEq.

(* maps for seq don't have empty values *)
(* TODO generalize to arbitrary predicates? *)
Section Regular.
Context {disp : unit} {K : orderType disp} {V : Type}.

Definition regular (t : kvtree K (seq V)) :=
  forall k, oapp (negb \o nilp (T:=V)) true (lookup t k).

Remark regular_leaf : regular leaf.
Proof. by []. Qed.

Lemma regular_del k t :
  invariant t -> regular t ->
  regular (delete k t).1.
Proof.
rewrite /regular=>H R l.
by rewrite lookup_delete //=; case: eqP.
Qed.

Lemma regular_ins k v t :
  invariant t -> regular t ->
  regular (upsert k (cons v) [::v] t).1.
Proof.
rewrite /regular=>H R l.
rewrite lookup_upsert //=; case: eqP=>//= {l}_.
by case: (lookup t k).
Qed.

End Regular.

(*
From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.

Set Extraction Flag 522.
Extract Inlined Constant negb => "not".
Extract Inlined Constant idP => "".
Extract Inlined Constant eqn => "equal".  (* ints! *)
Extract Inlined Constant size => "List.length".
Extract Inlined Constant cat => "List.append".
Extract Inductive reflect => bool [ true false ].
Extract Inductive alt_spec => bool [ true false ].
Extract Inductive eq_xor_neq => bool [ true false ].
Extract Inductive leq_xor_gtn => bool [ true false ].
Extract Inductive ltn_xor_geq => bool [ true false ].

Extract Inductive Derivable2 => "( * )" [ "" ].

Extraction "ext.ml" lookup upsert delete foldr_v.
*)
