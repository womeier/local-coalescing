(** Round-trip pipeline: parse a Wasm binary and print it back. *)

From Wasm Require Import binary_format_parser binary_format_printer.
From Wasmopt Require Import coalesce_locals.
From Stdlib Require Import Strings.String.

Open Scope string_scope.

Definition parse_and_print (input : string) : option string :=
  match run_parse_module_str input with
  | Some m => Some (string_of_list_byte (binary_of_module m))
  | None => None
  end.

Definition parse_optimize_print (input : string) : option string :=
  match run_parse_module_str input with
  | Some m => Some (string_of_list_byte (binary_of_module (coalesce_module m)))
  | None => None
  end.
