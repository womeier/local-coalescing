let read_file filename =
  let ic = open_in_bin filename in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic; s

let write_file filename s =
  let oc = open_out_bin filename in
  output_string oc s; close_out oc

let char_list_of_string s =
  let n = String.length s in
  let rec aux i acc = if i < 0 then acc else aux (i - 1) (s.[i] :: acc) in
  aux (n - 1) []

let string_of_char_list l =
  let buf = Buffer.create 16 in
  List.iter (Buffer.add_char buf) l; Buffer.contents buf

(* current RSS and peak RSS, in GB, from /proc/self/status *)
let mem () =
  let ic = open_in "/proc/self/status" in
  let cur = ref 0.0 and peak = ref 0.0 in
  (try while true do
     let l = input_line ic in
     let grab () = float_of_string (List.nth (String.split_on_char ' '
       (String.concat " " (String.split_on_char '\t' l))
       |> List.filter (fun s -> s <> "")) 1) /. 1e6 in
     if String.length l > 6 && String.sub l 0 6 = "VmRSS:" then cur := grab ()
     else if String.length l > 6 && String.sub l 0 6 = "VmHWM:" then peak := grab ()
   done with End_of_file -> ());
  close_in ic; (!cur, !peak)

let phase name f =
  let t = Unix.gettimeofday () in
  let r = f () in
  let (cur, peak) = mem () in
  Printf.printf "  %-10s %7.2fs   rss %6.2f GB   peak %6.2f GB\n%!"
    name (Unix.gettimeofday () -. t) cur peak;
  r

let () =
  let input = read_file Sys.argv.(1) in
  let cl = char_list_of_string input in
  let m = phase "parse" (fun () ->
    match Pipeline.run_parse_module_str cl with
    | Some m -> m | None -> prerr_endline "Parse error"; exit 1) in
  let m' = phase "coalesce" (fun () -> Pipeline.coalesce_module m) in
  let bytes = phase "print" (fun () ->
    Pipeline.string_of_list_byte (Pipeline.binary_of_module m')) in
  write_file Sys.argv.(2) (string_of_char_list bytes)
