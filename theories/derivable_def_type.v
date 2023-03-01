From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq.
From ipcssr Require Import forms derivations.

(*******************************************************************)

Variant Derivable {A} (ctx : seq (form A)) (a : form A) : Type :=
  Derivable_Intro t of derives ctx t a.

Variant Derivable2 {A} (ctx : seq (form A)) (a b : form A) : Type :=
  Derivable2_Intro of Derivable ctx a & Derivable ctx b.
