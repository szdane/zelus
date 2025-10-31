(* gen.ml  ─  Zelus AST → Liquid Fixpoint text *****************************)

open Zparsetree
open Pprint               

let fresh =
  let counter = ref 8 in
  fun () -> incr counter; !counter

(* Turn one Erefinement into a  (“bind …”) line and return its fresh id  *)
let bind_line_of_ty (ty : type_expression) : int * string =
  match ty.desc with
  | Erefinement ((v, base_ty), pred_ty) ->
      let id      = fresh () in
      let base_s  = Pprint.string_of_type base_ty in
      let line    = Printf.sprintf "bind %d %s : {v:%s | %s}" id v base_s (Pprint.string_of_expr pred_ty) in
      (id, line)
  | _ ->
      invalid_arg "Environment element is not a refinement type"

let to_fq
    ~(cid : int)
    ~(lhs  : type_expression)
    ~(rhs  : type_expression)
    ~(env  : type_expression list)
    ()
    : string
  =
  (* 1 . produce one bind line per env-type, gather their ids *)
  let ids, bind_lines = List.split (List.map bind_line_of_ty env) in

  (* 2 . pretty-print lhs / rhs *)
  let lhs_s = Pprint.string_of_type lhs in
  let rhs_s = Pprint.string_of_type rhs in

  (* 3 . build the constraint block as plain text *)
  let constraint_lines = [
    "constraint:";
    Printf.sprintf "  env [%s]"(String.concat ";" (List.map string_of_int ids));
    Printf.sprintf "  lhs %s" lhs_s;
    Printf.sprintf "  rhs %s" rhs_s;
    Printf.sprintf "  id %d tag []" cid
  ] in

  String.concat "\n" (bind_lines @ ["" (* blank line *)] @ constraint_lines)

(* let () =
  if Array.length Sys.argv = 2 then begin
    let out_file = Sys.argv.(1) in

    let loc  = Zlocation.no_location in
    let base = { desc = Etypeconstr (Name "int", []); loc } in
    let pred =
      { desc = Eapp ({ app_inline = false; app_statefull = false },
                     { desc = Evar (Name "<"); loc },
                     [ { desc = Evar (Name "v"); loc };
                       { desc = Econst (Eint 0); loc } ]);
        loc }
    in
    let ty = { desc = Erefinement (("v", base), pred); loc } in

    let lbase = { desc = Etypeconstr (Name "int", []); loc } in
    let lpred =
      { desc = Eapp ({ app_inline = false; app_statefull = false },
                     { desc = Evar (Name "<"); loc },
                     [ { desc = Evar (Name "v"); loc };
                       { desc = Econst (Eint 5); loc } ]);
        loc }
    in
    let lty = { desc = Erefinement (("v", lbase), lpred); loc } in

    let fq_text = to_fq ~cid:1 ~lhs:lty ~rhs:ty ~env:[ty] () in

    let oc = open_out out_file in
    output_string oc fq_text;  close_out oc;
    Printf.printf "Wrote %s\n" out_file
  end *)