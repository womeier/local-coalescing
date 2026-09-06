(** Extraction to OCaml. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.

(* ExtrOcamlNatInt maps the *type* [nat] to [int], but leaves these comparisons
   as recursions that walk both arguments down to zero one [S] at a time -- so
   comparing two instruction positions costs O(position) rather than O(1).
   [expire_active] runs [Nat.leb] over the active list once per interval, which
   made [linear_scan] 8.4s of the 8.6s the pass spent on sha.wasm. *)
Extract Inlined Constant Nat.leb => "(<=)".
Extract Inlined Constant Nat.ltb => "(<)".
Extract Inlined Constant Nat.eqb => "(=)".

From Wasm Require Import binary_format_parser binary_format_printer.
From Wasmopt Require Import pipeline.

Extraction Language OCaml.

Extraction "pipeline" parse_and_print parse_optimize_print.
