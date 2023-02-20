From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq.
From ipcssr Require Import forms derivations.

(*******************************************************************)

Variant Derivable {A} (ctx : seq (form A)) (a : form A) : Prop :=
  Derivable_Intro t : derives ctx t a -> Derivable ctx a.

Variant Derivable2 {A} (ctx : seq (form A)) (a b : form A) : Prop :=
  Derivable2_Intro : Derivable ctx a -> Derivable ctx b -> Derivable2 ctx a b.
