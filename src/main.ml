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

let () =
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
