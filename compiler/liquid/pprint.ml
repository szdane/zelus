(* 

Usage: 
ocamlfind ocamlopt -I ../global -I ../parsing ../global/zlocation.ml ../parsing/zparsetree.ml pprint.ml -o example

  *)


open Zelus
open Typing    

open Zident
open Lident
open Global
open Modules
open Deftypes
open Ztypes
open Typerrors

open Zmisc
open Zlocation
open Format

open List
open Hashtbl
open Str

let string_of_lident = function
  | Name n                     -> n
  | Modname { qual; id }       -> qual ^ "." ^ id

let string_of_zident n = n.source


let string_of_basic_type (t : type_expression) =
  match t.desc with
  | Etypeconstr (Name "int",  [])  -> "Int"
  | Etypeconstr (Name "bool", [])  -> "Bool"
  | Etypeconstr (Name "real", [])  -> "Real"
  | Etypeconstr (ln,          _)   -> string_of_lident ln
  | _                              -> "<complex-type>"


  let rec string_of_expr (e : exp) =
    match e.e_desc with
    | Eglobal {lname; _}                   -> string_of_lident lname
    | Elocal zi                         -> string_of_zident zi
    | Econst (Eint n)                   -> string_of_int n
    | Econst (Ebool b)                  -> string_of_bool b
    | Econst (Efloat f)                 -> string_of_float f
    | Econst (Echar c)                  -> String.make 1 c
    | Econst (Estring s)                -> Printf.sprintf "\"%s\"" s
  
    | Eapp (_, { e_desc = Eglobal {lname = Name "not"; _}; _ }, [e1]) ->
        "!(" ^ string_of_expr e1 ^ ")"
  
    | Eapp (_, { e_desc = Eglobal {lname = Name op ; _}; _ }, [e1; e2])
      when List.mem op ["<"; "<="; ">"; ">="; "="; "!="; "&&"; "||"; "+"; "-"; "*"; "/"] ->
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
