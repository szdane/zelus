(* 

Usage: 
ocamlfind ocamlopt -I ../global -I ../parsing ../global/zlocation.ml ../parsing/zparsetree.ml pprint.ml -o example

  *)


open Zparsetree         


let rec string_of_longname = function
  | Name n                     -> n
  | Modname { qual; id }       -> qual ^ "." ^ id

let string_of_basic_type (t : type_expression) =
  match t.desc with
  | Etypeconstr (Name "int",  [])  -> "Int"
  | Etypeconstr (Name "bool", [])  -> "Bool"
  | Etypeconstr (Name "real", [])  -> "Real"
  | Etypeconstr (ln,          _)   -> string_of_longname ln
  | _                              -> "<complex-type>"


  let rec string_of_expr (e : exp) =
    match e.desc with
    | Evar ln                           -> string_of_longname ln
  
    | Econst (Eint n)                   -> string_of_int n
    | Econst (Ebool b)                  -> string_of_bool b
    | Econst (Efloat f)                 -> string_of_float f
    | Econst (Echar c)                  -> String.make 1 c
    | Econst (Estring s)                -> Printf.sprintf "\"%s\"" s
  
    | Eapp (_, { desc = Evar (Name "not"); _ }, [e1]) ->
        "!(" ^ string_of_expr e1 ^ ")"
  
    | Eapp (_, { desc = Evar (Name op); _ }, [e1; e2])
      when List.mem op ["<"; "<="; ">"; ">="; "="; "!="; "&&"; "||"] ->
        Printf.sprintf "%s %s %s"
          (string_of_expr e1) op (string_of_expr e2)
  
    | _ -> "<complex-expr>"


let rec string_of_type (t : type_expression) =
  match t.desc with
  | Erefinement ((v, base_ty), pred) ->
      Printf.sprintf "{%s:%s | %s}"
        v (string_of_basic_type base_ty) (string_of_expr pred)
  | _ -> string_of_basic_type t        

(* 
let () =
  let loc  = Zlocation.no_location in        
  let var  = "v" in
  let base = { desc = Etypeconstr (Name "int", []); loc } in
  let lt0  =
    { desc = Eapp ({ app_inline = false; app_statefull = false },
                   { desc = Evar (Name "<"); loc },
                   [ { desc = Evar (Name var); loc };
                     { desc = Econst (Eint 0);          loc } ]);
      loc }
  in
  let ty = { desc = Erefinement ((var, base), lt0); loc } in
  print_endline (string_of_type ty) *)
  (* prints:  {v:Int | v < 0} *)
