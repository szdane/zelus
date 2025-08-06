(**********************************************************************
liquidrefinement.ml – prototype integration of the Zelus AST to 
                  Liquid Fixpoint translation to the compiler
---------------------------------------------------------------------
For each binding we
1. synthesise a singleton type for the rhs,
2. query LiqF to check the singleton ≤ refinement type,
3. if SAFE we extend Γ with `x : annotation`.

Usage with the test AST:
ocamlfind ocamlopt -I ../global -I ../parsing ../global/zlocation.ml ../parsing/zparsetree.ml pprint.ml gen.ml liquidrefinement.ml testliquid.ml -o example_
./example_

Usage with the compiler: change z3refinement.implementation_list to liquidrefinement.implementation_list
***********************************************************************)

open Zelus
open Typing
open Gen 

open Zident
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

let dummy_loc = Zlocation.no_location

let mk_type desc =
  { desc  = desc; loc = dummy_loc}

let literal_and_base = function
  | Eint  n  -> string_of_int n  , "Int"
  | Efloat f -> string_of_float f, "Real"
  | Ebool b  -> string_of_bool b , "Bool"
  | Estring s -> Printf.sprintf "%S" s , "String"
  | _         -> failwith "Unsupported literal in Liquid prototype"

let singleton_type_of_const (c : Zparsetree.immediate) : type_expression =
  let _lit_s, base_name = literal_and_base c in
  let base_ty  = mk_type (Etypeconstr (Name (String.lowercase_ascii base_name), [])) in
  let v_var    = { e_desc = Elocal ({num = 0; source = "v"}); e_loc = dummy_loc } in
  let lit_exp  = { e_desc = Econst c;          loc = dummy_loc } in
  let op_exp   = { e_desc = Elocal ({num = 1; source = "="});  loc = dummy_loc } in
  let pred_exp = { e_desc = Eapp ({ app_inline = false; app_statefull = false },
                                  op_exp, [v_var; lit_exp]);
                  loc  = dummy_loc } in
  mk_type (Erefinement (("v", base_ty), pred_exp))

let singleton_type_of_var var base_ty = 
  let v_var    = { desc = Elocal ({num = 0; source = "v"}); loc = dummy_loc } in
  let lit_exp  = { desc = Elocal ({num = 1; source = var});  loc = dummy_loc } in
  let op_exp   = { desc = Elocal ({num = 2; source = "="});  loc = dummy_loc } in
  let pred_exp = { desc = Eapp ({ app_inline = false; app_statefull = false },
                                  op_exp, [v_var; lit_exp]);
                  loc  = dummy_loc } in
  mk_type (Erefinement (("v", base_ty), pred_exp))

let singleton_type_of_app eapp base_ty= 
  match eapp.desc with 
  | Eapp(options, op, params) ->
  let v_var    = { desc = Evar (Name "v"); loc = dummy_loc } in
  let op_exp   = { desc = Evar (Name "=");  loc = dummy_loc } in
  let lit_exp = {desc = Eapp (options, 
  {desc = op.desc; loc = dummy_loc}, params); loc = dummy_loc} in
  let pred_exp = { desc = Eapp ({ app_inline = false; app_statefull = false },
                                  op_exp, [v_var; lit_exp]);
                  loc  = dummy_loc } in
  mk_type (Erefinement (("v", base_ty), pred_exp))
  | _ -> failwith(Printf.sprintf "It's not an Eapp")


module Env = Map.Make (String)
let gamma : type_expression Env.t ref = ref Env.empty
let add_binding name ty = 
  match ty.desc with
    | Erefinement((var, base_ty), lpred) -> gamma := Env.add name ({desc = Erefinement((name, base_ty), lpred); loc = dummy_loc}) !gamma
    | _ -> failwith(Printf.sprintf "It's not a refinement type")
let current_env ()      = !gamma |> Env.bindings |> List.map snd



let fixpoint_is_safe (fq_txt : string) : bool =
  let tmp = Filename.temp_file "liq_query" ".fq" in
  let oc  = open_out tmp in
  output_string oc fq_txt; close_out oc;
  let status = Sys.command (Printf.sprintf "fixpoint %s" (Filename.quote tmp)) in
  (* Sys.remove tmp; *)
  Printf.eprintf "[LiqF] kept query file: %s\n%!" tmp;
  status = 0

let process_const_decl ~(name:string)
                        ~(rhs_ty:type_expression)
                        ~(const:Zparsetree.immediate) : unit =
  let lhs_ty   = singleton_type_of_const const in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs_ty ~env:(current_env ()) () in
  if fixpoint_is_safe fq_query then
    add_binding name rhs_ty
  else
    failwith (Printf.sprintf "Liquid type error: constant %s does not satisfy its annotation" name)

let process_var_decl name rhs_ty var = 
  match rhs_ty.desc with 
  | Erefinement((_, base_ty), _) ->
  let lhs_ty = singleton_type_of_var var base_ty in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs_ty ~env:(current_env ()) () in
  if fixpoint_is_safe fq_query then
    add_binding name rhs_ty
  else
    failwith (Printf.sprintf "Liquid type error: var %s does not satisfy its annotation" name)
  |_ -> failwith (Printf.sprintf "Not a refinement type")


let process_app_decl name rhs_ty eapp = 
  match rhs_ty.desc with 
  | Erefinement((_, base_ty), _) ->
  let lhs_ty = singleton_type_of_app eapp base_ty in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs_ty ~env:(current_env ()) () in
  if fixpoint_is_safe fq_query then
    add_binding name rhs_ty
  else
    failwith (Printf.sprintf "Liquid type error: var %s does not satisfy its annotation" name)
  |_ -> failwith (Printf.sprintf "Not a refinement type")

let implementation impl =
  match impl.desc with
  | Econstdecl (id, rhs_ty, _is_static, { desc = Econst c; _ }) ->
      process_const_decl ~name:id ~rhs_ty ~const:c
  | Econstdecl (id, rhs_ty, is_static, { desc = Evar v; _}) -> process_var_decl id rhs_ty v
  | Econstdecl (id, rhs_ty, is_static, eapp) -> process_app_decl id rhs_ty eapp
  | _ -> ()

let implementation_list ff (impl_list) =
List.iter implementation impl_list;
impl_list
