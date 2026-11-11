(* Exercise the actual compiler and Fixpoint, including which T-DER-FIN
   premise rejects a negative example. A parser/typing/solver crash must not
   count as an expected verification failure. *)
let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let write path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel contents)

let rec clean path =
  if Sys.is_directory path then begin
    Array.iter (fun name -> clean (Filename.concat path name)) (Sys.readdir path);
    Unix.rmdir path
  end else Sys.remove path

let run directory =
  let test_root = if Sys.file_exists "hybrid_good" then "." else "test" in
  let stdlib_source = if test_root = "." then "stdlib.zli" else "lib/std/stdlib.zli" in
  Unix.putenv "ZELUS_FQ_DUMP_DIR" (Filename.concat directory "queries");
  write (Filename.concat directory "stdlib.zli") (read stdlib_source);
  Initial.set_no_stdlib ();
  Compiler.interface "Stdlib" (Filename.concat directory "stdlib");
  Zmisc.default_used_modules := ["Stdlib"];
  Zmisc.load_path := directory :: !Zmisc.load_path;
  Zmisc.verify := true;
  let count = ref 0 in
  List.iter (fun category ->
    let path = Filename.concat test_root category in
    Array.to_list (Sys.readdir path)
    |> List.filter (fun name -> Filename.check_suffix name ".zls")
    |> List.sort String.compare
    |> List.iter (fun filename ->
      let source = read (Filename.concat path filename) in
      let prefix = Filename.concat directory (Filename.chop_extension filename) in
      write (prefix ^ ".zls") source;
      Modules.clear ();
      Utilities.gamma := Utilities.Env.empty;
      Utilities.gamma1 := Utilities.Env.empty;
      Hashtbl.clear Utilities.fun_sigs;
      Hashtbl.clear Liquidrefinement.init_table;
      Hashtbl.clear Liquidrefinement.hybrid_init_table;
      let compile () = Compiler.compile
        (String.capitalize_ascii (Filename.basename prefix)) prefix in
      if category = "hybrid_good" then compile ()
      else begin
        let ending = Str.search_forward (Str.regexp_string " *)") source 0 in
        let expected = String.sub source 3 (ending - 3) in
        match compile () with
        | () -> failwith (filename ^ ": unexpectedly accepted")
        | exception Failure message ->
            (try ignore (Str.search_forward (Str.regexp_string expected) message 0)
             with Not_found -> failwith (filename ^ ": wrong rejection: " ^ message))
      end;
      incr count)) ["hybrid_good"; "hybrid_bad"];
  Printf.printf "%d scalar T-DER-FIN compiler/solver tests passed.\n" !count

let () =
  if not (Lazy.force Liquidrefinement.fixpoint_available) then
    print_endline "SKIP hybrid_typing: fixpoint is not installed"
  else begin
    let directory = Filename.temp_file "zelus_hybrid_typing_" "" in
    Sys.remove directory;
    Unix.mkdir directory 0o700;
    Fun.protect ~finally:(fun () -> clean directory) (fun () -> run directory)
  end
