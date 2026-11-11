(* Exercise environment selection through the compiler and the real solver.
   Wrong annotations must fail verification, rather than a parser/solver crash. *)
let write path contents =
  let channel = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel contents)

let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let rec clean path =
  if Sys.is_directory path then begin
    Array.iter (fun name -> clean (Filename.concat path name)) (Sys.readdir path);
    Unix.rmdir path
  end else Sys.remove path

let counter head lower = Printf.sprintf {|let node exec () : {(a:float)*(b:float)|true} =
  let rec init xk1 = 0.
  and (xk : {xk:float | xk = 0. && nxt(globally(xk = last_xk1 && xk >= 1.))}) = last xk1
  and (xk1 : {xk1:float | xk1 = %s && nxt(globally(xk1 = xk +. 1. && xk1 >= %s))}) = xk +. 1.
  in xk, xk1
|} head lower

let cases = [
  "counter", counter "1." "2.", true;
  "wrong_head", counter "2." "2.", false;
  "wrong_later", counter "1." "3.", false;
  (* If the head [x = 0] leaks into the later environment, it contradicts
     the actual later value and can make this false obligation vacuous. *)
  "inconsistent_head", {|let node exec () : {r:int | true} =
  let rec (x : {q:int | q = 0 && nxt(globally(q = 1))}) = 0 fby 1
  and (y : {q:int | q = 0 && nxt(globally(q = 2))}) = x + 0
  in y
|}, false;
  "fby_tail", {|let node exec () : {r:int | true} =
  let rec (x : {q:int | q = 0 && nxt(globally(q = 1))}) = 0 fby 1
  and (y : {q:int | q = 0 && nxt(globally(q = 1))}) = x + 0
  in y
|}, true;
  "global_fact", {|let node exec () : {r:int | true} =
  let rec (x : {q:int | globally(q = 1)}) = 1
  and (y : {q:int | globally(q = 2)}) = x + 1
  in y
|}, true;
  "constant_call", {|let node nonnegative (a : {q:int | globally(q >= 0)}) : {r:int | true} = a
let b : {q:int | q = 5} = 5
let node exec () : {r:int | true} =
  let (y : {q:int | true}) = nonnegative(b) in y
|}, true;
]

let run directory =
  let stdlib = if Sys.file_exists "stdlib.zli" then "stdlib.zli" else "lib/std/stdlib.zli" in
  write (Filename.concat directory "stdlib.zli") (read stdlib);
  Unix.putenv "ZELUS_FQ_DUMP_DIR" (Filename.concat directory "queries");
  Initial.set_no_stdlib ();
  Compiler.interface "Stdlib" (Filename.concat directory "stdlib");
  Zmisc.default_used_modules := ["Stdlib"];
  Zmisc.load_path := directory :: !Zmisc.load_path;
  Zmisc.verify := true;
  List.iter (fun (name, source, accepted) ->
    let prefix = Filename.concat directory name in
    write (prefix ^ ".zls") source;
    Modules.clear ();
    Utilities.gamma := Utilities.Env.empty;
    Utilities.gamma1 := Utilities.Env.empty;
    Hashtbl.clear Utilities.fun_sigs;
    Hashtbl.clear Liquidrefinement.init_table;
    Hashtbl.clear Liquidrefinement.hybrid_init_table;
    match Compiler.compile (String.capitalize_ascii name) prefix with
    | () -> if not accepted then failwith (name ^ ": unexpectedly accepted")
    | exception Failure message ->
        if accepted then failwith (name ^ ": " ^ message);
        let expected = "Liquid type error:" in
        if String.length message < String.length expected
           || String.sub message 0 (String.length expected) <> expected then
          failwith (name ^ ": wrong rejection: " ^ message)
  ) cases;
  Printf.printf "%d temporal environment compiler/solver tests passed.\n" (List.length cases)

let () =
  if not (Lazy.force Liquidrefinement.fixpoint_available) then
    print_endline "SKIP temporal_environment: fixpoint is not installed"
  else begin
    let directory = Filename.temp_file "zelus_temporal_environment_" "" in
    Sys.remove directory;
    Unix.mkdir directory 0o700;
    Fun.protect ~finally:(fun () -> clean directory) (fun () -> run directory)
  end
