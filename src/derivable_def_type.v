From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import seq.
From ipcssr Require Import forms derivations.

(*******************************************************************)

Variant Derivable {A} (context : seq (form A)) (a : form A) : Type :=
  Derivable_Intro t : derives context t a -> Derivable context a.

Variant Derivable2 {A} (context : seq (form A)) (a b : form A) : Type :=
  Derivable2_Intro : Derivable context a -> Derivable context b -> Derivable2 context a b.
