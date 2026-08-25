(** Extraction to OCaml. *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

From Wasm Require Import binary_format_parser binary_format_printer.
From Wasmopt Require Import pipeline.

Extraction Language OCaml.

Extraction "pipeline" parse_and_print parse_optimize_print.
