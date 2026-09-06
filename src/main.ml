let read_file filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  s

let write_file filename s =
  let oc = open_out_bin filename in
  output_string oc s;
  close_out oc

let char_list_of_string s =
  let n = String.length s in
  let rec aux i acc =
    if i < 0 then acc
    else aux (i - 1) (s.[i] :: acc)
  in
  aux (n - 1) []

let string_of_char_list l =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) l;
  Buffer.contents buf

(* WasmCert's parser and printer recurse once per instruction (List.map and
   friends are not tail-recursive), so the stack grows with the size of the
   function being processed: ~5.5MB for sha.wasm, ~45MB for a 412k-instruction
   CertiRocq benchmark.  The usual 8MB default is not enough, and the failure
   is a bare Stack_overflow rather than anything diagnostic.

   The limit has to be raised *before* exec: Linux places the mmap region
   using RLIMIT_STACK as it stands at exec time, so a process that raises its
   own limit afterwards still cannot grow the stack past that placement.  So
   re-exec ourselves once through sh with the limit lifted, marking the
   environment so the second run proceeds normally.  If anything about that
   fails we fall through and run anyway -- small inputs do not need it. *)
let raise_stack_limit () =
  if Sys.getenv_opt "WASM_OPT_CERT_STACK" = None then begin
    Unix.putenv "WASM_OPT_CERT_STACK" "1";
    let script =
      "{ ulimit -s unlimited || ulimit -s \"$(ulimit -Hs)\"; } 2>/dev/null; \
       exec \"$0\" \"$@\"" in
    let rest = Array.sub Sys.argv 1 (Array.length Sys.argv - 1) in
    let argv =
      Array.append [| "/bin/sh"; "-c"; script; Sys.executable_name |] rest in
    try Unix.execv "/bin/sh" argv with Unix.Unix_error _ -> ()
  end

let () =
  raise_stack_limit ();
  if Array.length Sys.argv <> 3 then begin
    Printf.eprintf "Usage: %s <input.wasm> <output.wasm>\n" Sys.argv.(0);
    exit 1
  end;
  let input = read_file Sys.argv.(1) in
  match Pipeline.parse_optimize_print (char_list_of_string input) with
  | None ->
    Printf.eprintf "Parse error\n";
    exit 1
  | Some output ->
    write_file Sys.argv.(2) (string_of_char_list output)
