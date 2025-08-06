(* gen.ml ─ Zelus AST  ➜  Liquid-Fixpoint text 
Usage: ocamlfind ocamlopt -I ../global -I ../parsing ../global/zlocation.ml ../parsing/zparsetree.ml pprint.ml gen_.ml -o example_

****************************)

open Zparsetree

(* ====================================================================== *)
(* Pretty-printing helpers                                                *)
(* ====================================================================== *)

(** string_of_longname "M.N.x"  →  "M.N.x" *)
let rec string_of_longname = function
  | Name s                     -> s
  | Modname { qual; id }       -> qual ^ "." ^ id

(** Rudimentary expression printer (just enough for predicates) *)
let rec string_of_expr (e : exp) =
  match e.desc with
  | Evar ln                           -> string_of_longname ln
  | Econst (Eint  n)                  -> string_of_int  n
  | Econst (Ebool b)                  -> string_of_bool b
  | Eapp (_, { desc = Evar (Name "not"); _ }, [e1]) ->
      "!(" ^ string_of_expr e1 ^ ")"
  | Eapp (_, { desc = Evar (Name op); _ }, [e1; e2]) ->
      Printf.sprintf "%s %s %s"
        (string_of_expr e1) op (string_of_expr e2)
  | _ -> "<expr>"

(** Extended type printer that also recognises  func(arity,[t1,…,tn])  *)
let rec string_of_type (t : type_expression) =
  match t.desc with
  | Etypeconstr (Name "int",  [])  -> "Int"
  | Etypeconstr (Name "bool", [])  -> "Bool"
  | Etypeconstr (Name "real", [])  -> "Real"

  (* ---- uninterpreted function ------------------------------------- *)
  | Etypeconstr (Name "func", arity_ty :: arg_tys) ->
      (* arity is encoded as a zero-arg type constructor whose name
         *is* the number, e.g.  Name "1"  or  Name "3".               *)
      let arity_s =
        match arity_ty.desc with
        | Etypeconstr (Name n, []) when
            String.for_all (fun c -> '0' <= c && c <= '9') n -> n
        | _ -> "?"
      in
      let args_s =
        "[" ^ String.concat "," (List.map string_of_type arg_tys) ^ "]"
      in
      "func(" ^ arity_s ^ "," ^ args_s ^ ")"

  (* ---- any other named constructor -------------------------------- *)
  | Etypeconstr (ln, _)          -> string_of_longname ln

  | Erefinement ((v, base), p)   ->
      Printf.sprintf "{%s:%s | %s}"
        v (string_of_type base) (string_of_expr p)

  | _                            -> "<type>"

(* ====================================================================== *)
(* Fresh id generator                                                     *)
(* ====================================================================== *)
let fresh =
  let c = ref 0 in
  fun () -> incr c; !c

(* ====================================================================== *)
(* Low-level helper: one env element ➜ (id, bind-line)                    *)
(* ====================================================================== *)
let bind_of_env (ty : type_expression) : int * string =
  match ty.desc with
  | Erefinement ((v, base_ty), _) ->
      let id  = fresh () in
      let bty = string_of_type base_ty in
      (id, Printf.sprintf "bind %d %s : {v:%s | true}" id v bty)

  (* uninterpreted func often comes in the same wrapper:                  *)
  | _ ->
      (* fabricate a dummy variable name if the AST doesn’t carry one     *)
      let id   = fresh () in
      let var  = "f" ^ string_of_int id in
      let bty  = string_of_type ty in
      (id, Printf.sprintf "bind %d %s : {v:%s | true}" id var bty)

(* ====================================================================== *)
(* Public API                                                             *)
(* ====================================================================== *)
let to_fq
    ~(cid : int)
    ~(lhs  : type_expression)
    ~(rhs  : type_expression)
    ~(env  : type_expression list)
    () : string
  =
  (* 1 ▪ env ➜ list of (id, bind-line) *)
  let ids, bind_lines = List.split (List.map bind_of_env env) in

  (* 2 ▪ pretty-print lhs / rhs *)
  let lhs_s = string_of_type lhs in
  (* let extra_pred = "(c = b => h c = h b)" in *)
  let rhs_s = string_of_type rhs in
  

  (* 3 ▪ assemble all text *)
  String.concat "\n"
    ( bind_lines
    @ [""]
    @ [ "constraint:"
      ; Printf.sprintf "  env [%s]" (String.concat ";" (List.map string_of_int ids))
      ; Printf.sprintf "  lhs %s" lhs_s
      ; Printf.sprintf "  rhs %s" rhs_s
      ; Printf.sprintf "  id %d tag []" cid ] )

(* ====================================================================== *)
(* Demo driver: run  `dune exec gen -- out.fq`                            *)
(* ====================================================================== *)
let () =
  if Array.length Sys.argv = 2 then begin
    let out = Sys.argv.(1) in
    let loc = Zlocation.no_location in

    (* {v:Int | v < 0} --------------------------------------------------- *)
    let int_ty = { desc = Etypeconstr (Name "int", []); loc } in
    let pred   =
      { desc = Eapp ({ app_inline=false; app_statefull=false },
                     { desc = Evar (Name "<"); loc },
                     [ { desc = Evar (Name "v"); loc };
                       { desc = Econst (Eint 0); loc } ]);
        loc }
    in
    let ref_ty = { desc = Erefinement (("v", int_ty), pred); loc } in


    let bool_ty = {desc = Etypeconstr (Name "bool", []); loc} in
    (* let ref_rhs = {desc = Erefinement (("z", bool_ty), pred_rhs); loc} in *)

    (* Uninterpreted function  h : func(1,[bool,bool]) ------------------- *)
  (* arity = "1" encoded at the type level *)
  (* b : Int *)
    let b_ty =
      { desc = Erefinement (("b", bool_ty),
              { desc = Econst (Ebool true); loc }); loc } in

    (* c : Int *)
    let c_ty =
      { desc = Erefinement (("c", bool_ty),
              { desc = Econst (Ebool true); loc }); loc } in

    let arity1   = { desc = Etypeconstr (Name "1", []); loc } in
    let bool_ty  = { desc = Etypeconstr (Name "bool", []); loc } in

    (* func(1,[Bool,Bool]) uses a flat list of type args,
      NOT an Etuple expression. *)
    let func_ty  =
      { desc = Etypeconstr (Name "func", [arity1; bool_ty; bool_ty]); loc }
    in
    let uf_ref_ty =
      { desc = Erefinement
          ( ("h", func_ty),
            { desc = Econst (Ebool true); loc });
        loc } in


    (* Build Fixpoint text ---------------------------------------------- *)
    let fq_text =
      to_fq ~cid:1
            ~lhs:ref_ty
            ~rhs:ref_ty
            ~env:[ref_ty; uf_ref_ty; b_ty; c_ty]
            ()
    in
    let oc = open_out out in
    output_string oc fq_text; close_out oc;
    Printf.printf "Wrote %s\n" out
  end
