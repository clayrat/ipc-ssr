From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq eqtype order.
From ipcssr Require Import avlmap trees forms kripke_trees normal_forms in_ngamma.

Section Le_Ks.
Context {disp : unit} {A : orderType disp}.

Fixpoint le_ni (ni1 ni2 : seq (nested_imp A)) : bool :=
  match ni1, ni2 with
  | [::], [::] => true
  | Undecorated x1 :: ni1,  Undecorated x2 :: ni2  => (x1 == x2) && le_ni ni1 ni2
  | Decorated x1 _ :: ni1,  Undecorated x2 :: ni2  => (x1 == x2) && le_ni ni1 ni2
  | Decorated x1 k1 :: ni1, Decorated x2 k2 :: ni2 => [&& x1 == x2, k1 == k2 & le_ni ni1 ni2]
  | _, _ => false
  end.

Lemma in_k_le (ni1 ni2 : seq (nested_imp A)) (x : nimp A) (k : kripke_tree A) :
  le_ni ni1 ni2 -> (Decorated x k) \in ni2 -> (Decorated x k) \in ni1.
Proof.
elim: ni1 ni2=>/= [|n1 ni1 IH]; case=>// n2 ni2.
rewrite !inE; case: n2=>[x2|x2 k2]; case: n1=>[x1|x1 k1] //=.
- by case/andP=>_; apply: IH.
- by case/andP=>_ H H2; rewrite (IH _ H H2) orbT.
case/and3P=>/eqP Ex /eqP Ek H; case/orP=>[/eqP|H2].
- by case=>->->; rewrite Ex Ek eqxx.
by rewrite (IH _ H H2) orbT.
Qed.

Lemma le_ni_refl : reflexive le_ni.
Proof. by elim=>//= a ni H; case a=>[x|x k]; rewrite !eqxx H. Qed.

Lemma le_ni_trans : transitive le_ni.
Proof.
elim=>[|n2 ni2 IH] ni1 ni3 /=; first by case: ni3.
case: ni1=>//=; case=>[x1|x1 k1] ni1; case: n2=>//.
- move=>x2 /andP [/eqP ->] H12; case: ni3=>//; case=>// x3 k3.
  by case/andP=>->/=; apply: IH.
- move=>x2 /andP [/eqP ->] H12; case: ni3=>//; case=>// x3 k3.
  by case/andP=>->/=; apply: IH.
move=>x2 k2; case/and3P=>/eqP->/eqP-> H12; case: ni3=>//; case=>[x3|x3 k3] ni3.
- by case/andP=>->/=; apply: IH.
by case/and3P=>->->/=; apply: IH.
Qed.

Lemma filter_deco i ni :
  {ni1 : seq (nested_imp A) |
     le_ni ni ni1 /\
     (forall x k, Decorated x k \in ni1 -> forces_t k (Atom i))}.
Proof.
elim: ni=>/= [|n ni]; first by exists [::].
case=>ni1 [H1 H2]; case: n=>[x|x k].
- by exists (Undecorated x :: ni1); rewrite eqxx.
case: k=>a s; case/boolP: (lookup a i)=>[L|_].
- exists (Decorated x (TNode a s ):: ni1); rewrite !eqxx /=; split=>// x0 k0.
  rewrite inE; case/orP=>[/eqP[{x0}_ ->]|H] //.
  by apply: (H2 _ _ H).
by exists (Undecorated x :: ni1); rewrite eqxx.
Qed.

(*****************************************************************)

Definition eqv_ni (ni1 ni2 : seq (nested_imp A)) : bool :=
  map nested_imp2nimp ni1 == map nested_imp2nimp ni2.

Lemma eqv_ni_refl : reflexive eqv_ni.
Proof. by rewrite /eqv_ni=>x; rewrite eqxx. Qed.

Lemma eqv_ni_sym : symmetric eqv_ni.
Proof. by rewrite /eqv_ni=>x y; rewrite eq_sym. Qed.

Lemma eqv_ni_trans : transitive eqv_ni.
Proof. by rewrite /eqv_ni =>y x z /eqP->. Qed.

Lemma le_eqv ni1 ni2 : le_ni ni1 ni2 -> eqv_ni ni1 ni2.
Proof.
elim: ni1 ni2=>[|n1 ni1 IH]; case=>[|n2 ni2] //=; first by case: n1.
rewrite /eqv_ni; case: n2=>[x2|x2 k2]; case: n1=>[x1|x1 k1] //=.
- by case/andP=>/eqP<- /IH /eqP ->.
- by case/andP=>/eqP<- /IH /eqP ->.
by case/and3P=>/eqP<- _ /IH /eqP ->.
Qed.

Lemma ge_eqv ni1 ni2 : le_ni ni2 ni1 -> eqv_ni ni1 ni2.
Proof. by rewrite eqv_ni_sym; apply: le_eqv. Qed.

(*****************************************************************)

Lemma inf_deco ni1 ni2 :
  eqv_ni ni1 ni2 ->
  {ni : seq (nested_imp A) |
    [/\ le_ni ni ni1,
        eqv_ni ni ni2 &
        (forall x k, Decorated x k \in ni ->
                     (Decorated x k \in ni1) || (Decorated x k \in ni2))]}.
Proof.
elim: ni1 ni2=>[|n1 ni1 IH]; case=>[|n2 ni2] //=.
- by move=>_; exists [::].
rewrite /eqv_ni /=; case/eqP=>E /eqP /IH [ni][L1 E2 H].
move: E; case: n2=>[x2|x2 k2]; case: n1=>[x1|x1 k1] /= {x2}<-.
- by exists (Undecorated x1 :: ni)=>/=; rewrite eqxx /= (eqP E2).
- exists (Decorated x1 k1 :: ni)=>/=; rewrite !eqxx /= (eqP E2); split=>// x0 k0.
  by rewrite !inE /= -orbA; case/orP=>[->|] // /H->; rewrite orbT.
- exists (Decorated x1 k2 :: ni)=>/=; rewrite eqxx /= (eqP E2); split=>// x0 k0.
  rewrite !inE /=; case/orP=>[->|] /=; first by rewrite orbT.
  by rewrite orbCA=>/H->; rewrite orbT.
exists (Decorated x1 k1 :: ni)=>/=; rewrite !eqxx /= (eqP E2); split=>// x0 k0.
rewrite !inE /= -orbA; case/orP=>[->|] //.
by case/H/orP=>-> /=; rewrite !orbT.
Qed.

Corollary eqv_nimps_eq ni1 ni2 :
  eqv_ni ni1 ni2 -> map nested_imp2nimp ni1 = map nested_imp2nimp ni2.
Proof. by move/eqP=>->. Qed.

Corollary in_ngamma_eqv work ds ni1 ni2 ai a c :
  eqv_ni ni1 ni2 ->
  in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
Proof. by move/eqP; apply: in_ngamma_ni_eq. Qed.

Corollary in_ngamma_le work ds ni1 ni2 ai a c :
  le_ni ni1 ni2 ->
  in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
Proof. move/le_eqv; apply: in_ngamma_eqv. Qed.

Corollary in_ngamma_ge work ds ni1 ni2 ai a c :
  le_ni ni2 ni1 ->
  in_ngamma work ds ni1 ai a c -> in_ngamma work ds ni2 ai a c.
Proof. move/ge_eqv; apply: in_ngamma_eqv. Qed.

(***********************************************************************)

Lemma le_app0 ni1 ni21 ni22 :
  le_ni ni1 (ni21 ++ ni22) ->
  {ni112 : (seq (nested_imp A) * seq (nested_imp A)) |
    ni1 = ni112.1 ++ ni112.2 /\ size ni112.1 = size ni21}.
Proof.
elim: ni21 ni1=>/= [|n21 ni21 IH]; first by move=>ni1 _; exists ([::], ni1)=>/=.
case=>[|n1 ni1] //= H.
have {}H: le_ni ni1 (ni21 ++ ni22).
- case: n1 H=>[x1|x1 k1]; case: n21=>[x21|x21 k21] //.
  - by case/andP.
  - by case/andP.
  by case/and3P.
case: (IH _ H)=>[[ni11 ni12]] /= [-><-].
by exists (n1 :: ni11, ni12).
Qed.

Lemma le_ni_app_nn ni1 ni2 ni3 ni4 x :
  size ni1 = size ni3 ->
  le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
  le_ni (ni1 ++ Undecorated x :: ni2) (ni3 ++ Undecorated x :: ni4).
Proof.
elim: ni1 ni3=>/=[|n1 ni1 IH] ni3.
- by move/esym/size0nil=>-> /=; rewrite eqxx.
case: ni3=>//= n3 ni3; case=>Es.
case: n1=>[x1|x1 k1]; case: n3=>[x3|x3 k3] //.
- by case/andP=>-> H /=; apply: IH.
- by case/andP=>-> H /=; apply: IH.
by case/and3P=>->-> H /=; apply: IH.
Qed.

Lemma le_ni_app_dn ni1 ni2 ni3 ni4 x k :
  size ni1 = size ni3 ->
  le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
  le_ni (ni1 ++ Decorated x k :: ni2) (ni3 ++ Undecorated x :: ni4).
Proof.
elim: ni1 ni3=>/=[|n1 ni1 IH] ni3.
- by move/esym/size0nil=>-> /=; rewrite eqxx.
case: ni3=>//= n3 ni3; case=>Es.
case: n1=>[x1|x1 k1]; case: n3=>[x3|x3 k3] //.
- by case/andP=>-> H /=; apply: IH.
- by case/andP=>-> H /=; apply: IH.
by case/and3P=>->-> H /=; apply: IH.
Qed.

Lemma le_ni_app_dd ni1 ni2 ni3 ni4 x k :
  size ni1 = size ni3 ->
  le_ni (ni1 ++ ni2) (ni3 ++ ni4) ->
  le_ni (ni1 ++ Decorated x k :: ni2) (ni3 ++ Decorated x k :: ni4).
Proof.
elim: ni1 ni3=>/=[|n1 ni1 IH] ni3.
- by move/esym/size0nil=>-> /=; rewrite !eqxx.
case: ni3=>//= n3 ni3; case=>Es.
case: n1=>[x1|x1 k1]; case: n3=>[x3|x3 k3] //.
- by case/andP=>-> H /=; apply: IH.
- by case/andP=>-> H /=; apply: IH.
by case/and3P=>->-> H /=; apply: IH.
Qed.

End Le_Ks.
