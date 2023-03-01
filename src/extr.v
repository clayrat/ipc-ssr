From Coq Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From mathcomp Require Import ssreflect ssrbool ssrfun.
From mathcomp Require Import ssrnat seq order eqtype.
From ipcssr Require Import search.

Set Extraction Flag 522.
Set Extraction AccessOpaque.

Extract Inlined Constant negb => "not".
Extract Inlined Constant idP => "".

(* lists *)
Extract Inlined Constant size => "List.length".
Extract Inlined Constant cat => "(@)".
Extract Inlined Constant fst => "fst".

(* ints! *)
Extract Inlined Constant eqn => "(=)".
Extract Inlined Constant leq => "(<=)".
Extract Inlined Constant leqP => "(<=)".
Extract Inlined Constant ltnP => "(<)".
Extract Inlined Constant maxn => "Stdlib.max".

Extract Inductive reflect => bool [ true false ].
Extract Inductive alt_spec => bool [ true false ].
Extract Inductive leq_xor_gtn => bool [ true false ].
Extract Inductive ltn_xor_geq => bool [ true false ].
Extract Inductive eq_xor_neq => bool [ true false ].
Extract Inductive sum => "Either.t" [ "Either.Left" "Either.Right" ].

Extraction "src/search.ml" search.search.
