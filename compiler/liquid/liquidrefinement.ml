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
open Lident

open Zparsetree

let debug message =
  (* log debug message *)
  (* if !ref_verbose then (Printf.printf "[DEBUG] : %s\n" message)  *)
  (Printf.printf "[DEBUG] : %s\n" message)

let dummy_loc = Zlocation.no_location

let mk_type desc =
  { desc  = desc; loc = dummy_loc}


let to_zpt_kind kind = 
  match kind with 
    | Zelus.S -> Zparsetree.S
    | Zelus.A -> Zparsetree.A
    | Zelus.C -> Zparsetree.C
    | Zelus.D -> Zparsetree.D
    | Zelus.AD -> Zparsetree.AD
    | Zelus.AS -> Zparsetree.AS
    | Zelus.P -> Zparsetree.P

  let zident_opt_to_string_opt (o : Zident.t option) : string option =
    Option.map Zident.name o

    
let literal_and_base = function
(*TODO: Fix this issue with int vs other types*)
  | Deftypes.Eint  n  -> Zparsetree.Eint n  , "Int"
  | Deftypes.Efloat f -> Zparsetree.Efloat f, "Real"
  | Ebool b  -> Zparsetree.Ebool b, "Bool"
  | Estring s -> Zparsetree.Estring s , "String"
  | _         -> failwith "Unsupported literal in Liquid prototype"

let singleton_type_of_const e base_name=
  let base_ty  = mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), [])) in
  let v_var    = { desc = Zparsetree.Evar (Name "v"); loc = dummy_loc } in
  let op_exp   = { desc = Zparsetree.Evar (Name "=");  loc = dummy_loc } in
  let pred_exp = { desc = Zparsetree.Eapp ({ app_inline = false; app_statefull = false },
                                  op_exp, [v_var; e]);
                  loc  = dummy_loc } in
  mk_type (Zparsetree.Erefinement (("v", base_ty), pred_exp))


module Env = Map.Make (String)
let gamma : type_expression Env.t ref = ref Env.empty
let add_binding name ty = 
  match ty.desc with
    | Erefinement((var, base_ty), lpred) -> gamma := Env.add name ({desc = Erefinement((name, base_ty), lpred); loc = dummy_loc}) !gamma
    | _ -> failwith(Printf.sprintf "It's not a refinement type")
let current_env ()      = !gamma |> Env.bindings |> List.map snd


let fixpoint_is_safe (fq_txt : string) : bool =
  let tmp_dir = Filename.get_temp_dir_name () in
  let tmp = Filename.temp_file ~temp_dir:tmp_dir "liq_query" ".fq" in
  let oc = open_out tmp in
  output_string oc fq_txt;
  close_out oc;
  let status = Sys.command (Printf.sprintf "fixpoint %s" (Filename.quote tmp)) in
  Sys.remove tmp;
  status = 0

(* 
let rec vc_gen_exp_list exp_list = 
  match exp_list with
    | [] -> []
    | exp::tl -> {desc = vc_gen_expression exp ; loc = dummy_loc}::vc_gen_exp_list tl *)
  

let rec vc_gen_expression ({ e_desc = desc; e_loc = loc }) =
  match desc with
  | Zelus.Econst(i) -> Zparsetree.Econst(fst (literal_and_base i))
  | Zelus.Eglobal{lname = Name n} -> Zparsetree.Evar(Name n)
  | Zelus.Eglobal{lname = Modname qualid} -> Zparsetree.Evar(Name qualid.id)
  | Zelus.Elocal{num = i; source = n} -> Zparsetree.Evar(Name n)
  (* | Zelus.Etuple(exp_list) -> Zparsetree.Etuple(List.map (fun exp -> {desc = vc_gen_expression exp; loc = dummy_loc}) exp_list) *)
  | Zelus.Etuple(exp_list) -> failwith (Printf.sprintf "Not handling tuple for now")
  (* | Zelus.Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> Zparsetree.Eapp({ app_inline = i; app_statefull = r }, {desc = (vc_gen_expression e); loc = dummy_loc}, vc_gen_exp_list e_list) *)
  | Zelus.Eapp ({ app_inline = i; app_statefull = r }, e, e_list) ->
    Zparsetree.Eapp
      ( { app_inline = i; app_statefull = r }, { desc = vc_gen_expression e; loc = dummy_loc }, List.map (fun exp -> { desc = vc_gen_expression exp; loc = dummy_loc }) e_list )
  | Zelus.Eop(op, exp_list) -> (match op with 
      | Zelus.Eifthenelse -> failwith (Printf.sprintf "Not handling ifthenelse for now")
      | _ -> failwith (Printf.sprintf "Not handling this Eop for now")
    )
  | Zelus.Eblock(_) -> failwith (Printf.sprintf "Not handling Eblock for now")
  (* | Zelus.Elet(_,exp) -> match exp.e_desc with
      | Econst(_) -> implementation {desc = vc_gen_expression exp; loc = dummy_loc}
      | _ -> failwith (Printf.sprintf "Not handling non constant let for now") *)

let rec to_zpt_type (t : Zelus.type_expression) : Zparsetree.type_expression =
  let loc = dummy_loc in
  match t.desc with
  | Zelus.Etypeconstr (Name n, args) ->
      mk_type (Zparsetree.Etypeconstr (Name n, List.map to_zpt_type args))

  | Zelus.Etypetuple ts ->
      mk_type (Zparsetree.Etypetuple (List.map to_zpt_type ts))

  | Zelus.Erefinement ((vname, base_ty), pred_exp) ->
      let base_zpt = to_zpt_type base_ty in
      let pred_zpt = { desc = vc_gen_expression pred_exp; loc } in
      mk_type (Zparsetree.Erefinement ((vname, base_zpt), pred_zpt))

  | Zelus.Erefinementlabeledtuple (fields, pred_exp) ->
      let fields' =
        List.map (fun (nm, ty) -> (nm, to_zpt_type ty)) fields
      in
      let pred_zpt = { desc = vc_gen_expression pred_exp; loc } in
      mk_type (Zparsetree.Erefinementlabeledtuple (fields', pred_zpt))

  | Zelus.Etypefun (k, zopt, arg_t, out_t) ->
      mk_type (Zparsetree.Etypefun (to_zpt_kind k,
                                    zident_opt_to_string_opt zopt,
                                    to_zpt_type arg_t,
                                    to_zpt_type out_t))

  | _ -> failwith "to_zpt_type: constructor not supported here"
      

let run_fq name lhs rhs = 
  let fq_query = Gen.to_fq ~cid:5 ~lhs:lhs ~rhs:rhs ~env:(current_env ()) () in
  debug (Printf.sprintf "%s" fq_query);
  fixpoint_is_safe fq_query
  


let process_lhs_ty e_desc base e = 
  match e_desc with 
    | Zelus.Etuple(_) -> failwith (Printf.sprintf "The expression is tuple")
    | Zelus.Eop(Eifthenelse,i::t::el::[]) -> singleton_type_of_const {desc = (vc_gen_expression t); loc = dummy_loc} base
    | _ -> singleton_type_of_const {desc = (vc_gen_expression e); loc = dummy_loc} base



let process_eapp ~(name:string)
                        ~v ~ base ~op var_list
                        ~(e) =
  (* let base_ty = base.in *)
  let rhs = 
  match var_list with 
    | op_l :: [] -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Eapp ({ app_inline = false; app_statefull = false },
          { desc = Evar (Name op); loc = dummy_loc },
          [ { desc = vc_gen_expression (op_l); loc = dummy_loc} ]); loc= dummy_loc }); loc = dummy_loc} 
    | op_l :: op_r :: [] -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Eapp ({ app_inline = false; app_statefull = false },
          { desc = Evar (Name op); loc = dummy_loc },
          [ { desc = vc_gen_expression op_l; loc = dummy_loc};
            { desc = vc_gen_expression op_r; loc = dummy_loc } ]); loc= dummy_loc }); loc = dummy_loc} 
    | _ -> failwith (Printf.sprintf "More than 2 operators of an operator call")
  in
  (name, rhs)

let process_eq ~(name:string)
                        ~v ~ base ~op var_list
                        ~(e) =
  (* let base_ty = base.in *)
  let rhs = 
  match var_list with 
    | op_l :: [] -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Eapp ({ app_inline = false; app_statefull = false },
          { desc = Evar (Name op); loc = dummy_loc },
          [ { desc = vc_gen_expression (op_l); loc = dummy_loc} ]); loc= dummy_loc }); loc = dummy_loc} 
    | op_l :: op_r :: [] -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Eapp ({ app_inline = false; app_statefull = false },
          { desc = Evar (Name op); loc = dummy_loc },
          [ { desc = vc_gen_expression op_l; loc = dummy_loc};
            { desc = vc_gen_expression op_r; loc = dummy_loc } ]); loc= dummy_loc }); loc = dummy_loc} 
    | _ -> failwith (Printf.sprintf "More than 2 operators of an operator call")
  in
  (name, rhs)

let process_ite name v base var e = 
  let id, refinement = match var with 
    | Zelus.Eapp({ app_inline = bool1; app_statefull = bool2 },
      { e_desc = Zelus.Eglobal{lname = (Name op)}; _ },
      list) -> process_eapp name v base op list e 
    | _ -> failwith (Printf.sprintf "Not an Eapp in the ifthenelse predicate") in
  match e.e_desc with
    | Zelus.Eop(Eifthenelse,i::t::el::[]) -> (
      match refinement.desc with 
        | Zparsetree.Erefinement((id, base_ty), pred) -> (
      let implication_pos = {desc = Eapp ({ app_inline = false; app_statefull = false },
          { desc = Evar(Name "=>"); loc = dummy_loc },
          [ { desc = vc_gen_expression (i); loc = dummy_loc};
            pred ]); loc= dummy_loc } in
      let implication_neg = {desc = Eapp ({ app_inline = false; app_statefull = false },
      { desc = Evar(Name "=>"); loc = dummy_loc },
      [ { desc = Eapp({app_inline = true; app_statefull = false }, {desc = Evar(Name "not"); loc = dummy_loc }, [ {desc = vc_gen_expression (i); loc = dummy_loc}]); loc= dummy_loc }; pred]); loc = dummy_loc} in
      let rhs_pos = {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), implication_pos); loc = dummy_loc} in 
      let rhs_neg = {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), implication_neg); loc = dummy_loc} in 
      let lhs_ty_t = process_lhs_ty e.e_desc base e in
      let lhs_ty_e = singleton_type_of_const {desc = (vc_gen_expression el); loc = dummy_loc} base in 
      let is_safe_then = run_fq name lhs_ty_t rhs_pos in 
      let is_safe_else = run_fq name lhs_ty_e rhs_neg in
      if is_safe_else && is_safe_else then
        add_binding name refinement
      else
        failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)
        )
        | _ -> failwith (Printf.sprintf "Not a refinement type in the ifthenelse predicate"))
    | _ -> failwith (Printf.sprintf "Not an ifthenelse expression in e")

let process_bool name v base var e = 
  let rhs = 
  match var with 
  | Zelus.Econst(Ebool(b)) -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Econst(Ebool(b)); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Name id)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Modname qualid)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name qualid.id); loc= dummy_loc }); loc = dummy_loc} 
  | Elocal{source = id} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | _ -> failwith (Printf.sprintf "Not a boolean value/variable inside the predicate")

  in
  let lhs_ty   = process_lhs_ty e.e_desc base e in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs ~env:(current_env ()) () in
  debug (Printf.sprintf "%s" fq_query);
  match var with 
  | Zelus.Econst(Ebool(true)) -> add_binding name rhs
  | _ ->
    if fixpoint_is_safe fq_query then
      add_binding name rhs
    else
      failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)

let process_bool_eq name v base var e = 
  let rhs = 
  match var with 
  | Zelus.Econst(Ebool(b)) -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Econst(Ebool(b)); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Name id)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Modname qualid)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name qualid.id); loc= dummy_loc }); loc = dummy_loc} 
  | Elocal{source = id} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypeconstr (Name base, []); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | _ -> failwith (Printf.sprintf "Not a boolean value/variable inside the predicate")

  in
  let lhs_ty   = process_lhs_ty e.e_desc base e in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs ~env:(current_env ()) () in
  debug (Printf.sprintf "%s" fq_query);
  match var with 
  | Zelus.Econst(Ebool(true)) -> add_binding name rhs
  | _ ->
    if fixpoint_is_safe fq_query then
      add_binding name rhs
    else
      failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)
      
let process_bool_fun name v arg out var e a opt = 
  let rhs = 
  match var with 
  | Zelus.Econst(Ebool(b)) -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypefun (a, opt, {desc = Zparsetree.Etypeconstr(Name arg, []);loc = dummy_loc},  {desc = Zparsetree.Etypeconstr(Name out, []);loc = dummy_loc}); loc = dummy_loc }), { desc = Zparsetree.Econst(Ebool(b)); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Name id)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypefun (a, opt, {desc = Zparsetree.Etypeconstr(Name arg, []);loc = dummy_loc}, {desc = Zparsetree.Etypeconstr(Name out, []);loc = dummy_loc}); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | Eglobal{lname = (Modname qualid)} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypefun (a, opt, {desc = Zparsetree.Etypeconstr(Name arg, []);loc = dummy_loc}, {desc = Zparsetree.Etypeconstr(Name out, []);loc = dummy_loc}); loc = dummy_loc }), { desc = Zparsetree.Evar(Name qualid.id); loc= dummy_loc }); loc = dummy_loc} 
  | Elocal{source = id} -> {desc = Zparsetree.Erefinement((v, { desc = Zparsetree.Etypefun (a, opt, {desc = Zparsetree.Etypeconstr(Name arg, []);loc = dummy_loc}, {desc = Zparsetree.Etypeconstr(Name out, []);loc = dummy_loc}); loc = dummy_loc }), { desc = Zparsetree.Evar(Name id); loc= dummy_loc }); loc = dummy_loc} 
  | _ -> failwith (Printf.sprintf "Not a boolean value/variable inside the predicate")

  in
  let lhs_ty   = process_lhs_ty e.e_desc out e in
  let fq_query = Gen.to_fq ~cid:1 ~lhs:lhs_ty ~rhs:rhs ~env:(current_env ()) () in
  debug (Printf.sprintf "%s" fq_query);
  match var with 
    | Zelus.Econst(Ebool(true)) -> add_binding name rhs
    | _ ->
          if fixpoint_is_safe fq_query then
            add_binding name rhs
          else
            failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)

let process_and_run ~name:id ~v ~base:base ~op list  ~e= 
  let name, rhs = process_eapp ~name:id ~v ~base:base ~op list  ~e in
  let lhs  = process_lhs_ty e.e_desc base e in
  let is_safe = run_fq name lhs rhs in
  if is_safe then
    add_binding name rhs
  else
    failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)
  

let process_and_run_eq ~name:id ~v ~base:base ~op list  ~e= 
  let name, rhs = process_eq ~name:id ~v ~base:base ~op list  ~e in
  let lhs  = process_lhs_ty e.e_desc base e in
  let is_safe = run_fq name lhs rhs in
  if is_safe then
    add_binding name rhs
  else
    failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" name)

(* Prefer the original source name of an identifier so it matches Elocal {source=...} *)
let zident_pretty (z : Zident.t) : string =
  let s = Zident.name z in
  (* Strip a trailing _<digits> if present, e.g., "e_2" -> "e" *)
  let len = String.length s in
  let rec all_digits s i j =
    if i > j then true else
    let c = s.[i] in
    ('0' <= c && c <= '9') && all_digits s (i+1) j
  in
  try
    let i = String.rindex s '_' in
    if i + 1 < len && all_digits s (i+1) (len-1)
    then String.sub s 0 i
    else s
  with Not_found -> s

  let singleton_with ~(binder:string) (e:Zparsetree.exp) (base_name:string)
  : Zparsetree.type_expression =
  let base_ty = mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), [])) in
  let v_var   = { desc = Zparsetree.Evar (Name binder); loc = dummy_loc } in
  let eq_op   = { desc = Zparsetree.Evar (Name "=");  loc = dummy_loc } in
  let pred    = { desc = Zparsetree.Eapp ({ app_inline = false; app_statefull = false },
                                          eq_op, [v_var; e]);
                  loc = dummy_loc } in
  mk_type (Zparsetree.Erefinement ((binder, base_ty), pred))

  let rec zelus_var_name_of_pat (p : Zelus.pattern) : string =
    match p.p_desc with
    | Zelus.Evarpat id -> zident_pretty id
    | Zelus.Ealiaspat (p', _) -> zelus_var_name_of_pat p'
    | Zelus.Etypeconstraintpat (p', _) -> zelus_var_name_of_pat p'
    | _ -> failwith "Tuple let: component must be a variable (optionally aliased/annotated)"
  
  
  let process_tuple_let_eq (pat : Zelus.pattern) (rhs : Zelus.exp) : unit =

    let (xs, ann_zelus) =
      match pat.p_desc with
      | Etypeconstraintpat (bp, ann) ->
          (match bp.p_desc with
           | Etuplepat ps ->
               let names = List.map zelus_var_name_of_pat ps in 
                (names, ann)
           | _ -> failwith "Tuple let: expected tuple pattern")
      | _ -> failwith "Tuple let: expected type-constrained tuple pattern"
    in
    let es =
      match rhs.e_desc with
      | Zelus.Etuple es -> es
      | _ -> failwith "Tuple let: RHS must be a tuple expression"
    in
    if List.length xs <> List.length es then
      failwith "Tuple let: arity mismatch";
  
    
    let ann_zpt = to_zpt_type ann_zelus in
    let (bvars, bases, phi) =
      match ann_zpt.desc with
      | Zparsetree.Erefinementlabeledtuple (fields, phi) ->
          let bnames = List.map fst fields in
          let bsorts =
            List.map (fun (_n, ty) ->
              match ty.desc with
              | Zparsetree.Etypeconstr (Name b, []) -> b
              | _ -> failwith "Tuple let: each component base must be Etypeconstr(Name,[])") fields
          in
          (bnames, bsorts, phi)
      | _ -> failwith "Tuple let: expected labeled-tuple refinement {(vx,vy,...) | φ}"
    in
    let ar = List.length xs in
    if List.length bvars <> ar || List.length bases <> ar then
      failwith "Tuple let: annotation arity mismatch";
  
    
    let ghosts =
      List.mapi (fun i ei ->
        let bi   = List.nth bvars i in
        let base = List.nth bases i in
        let ei_z = { desc = vc_gen_expression ei; loc = dummy_loc } in
        singleton_with ~binder:bi ei_z base
      ) es
    in
    List.iteri (fun i ty ->
      let bi = List.nth bvars i in
      add_binding bi ty
    ) ghosts;
  
    
    let k       = ar - 1 in
    let bk      = List.nth bvars k in
    let base_k  = List.nth bases k in
    let lhs_k   = List.nth ghosts k in   (* {bk | bk = ek} *)
    let rhs_k   =
      mk_type (Zparsetree.Erefinement ((bk,
                 mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_k), []))),
                 phi))
    in
    if not (run_fq bk lhs_k rhs_k) then
      failwith "Liquid type error: tuple refinement not satisfied";
  
    
    for i = 0 to ar - 1 do
      let xi   = List.nth xs i in
      let base = List.nth bases i in
      let ty_i =
        mk_type (Zparsetree.Erefinement ((xi,
                   mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []))),
                   phi))
      in
      add_binding xi ty_i;

    done

  let process_scalar_eq base_pat ty_ann_zelus rhs =    
    debug (Printf.sprintf "Processing let eq with annotation");       
    let x =
    match base_pat.p_desc with
    | Evarpat id -> zident_pretty id
    | _ -> failwith "Let pattern must be a variable with a refinement annotation"
  in

  
  let ty_ann_zpt = to_zpt_type ty_ann_zelus in

  
  let base_name =
    match ty_ann_zpt.desc with
    | Zparsetree.Erefinement ((_v, base_ty), _pred) ->
        (match base_ty.desc with
          | Zparsetree.Etypeconstr (Name b, []) -> b
          | _ -> failwith "Refinement base must be Etypeconstr(Name,[])")
    | _ -> failwith "Expected refinement type on let-bound pattern"
  in

  
  let lhs_ty =
    singleton_type_of_const
      { desc = vc_gen_expression rhs; loc = dummy_loc }
      base_name
  in

  
  if run_fq x lhs_ty ty_ann_zpt then
    add_binding x ty_ann_zpt
  else
    failwith (Printf.sprintf
      "Liquid type error: let-bound %s does not satisfy its annotation" x)


let process_let_eq (eq : Zelus.eq) : unit =
  match eq.eq_desc with
  | EQeq (pat, rhs) -> begin
      match pat.p_desc with
      | Etypeconstraintpat (base_pat, ty_ann_zelus) -> begin
        match base_pat.p_desc with
        | Zelus.Etuplepat _ps ->
            
            process_tuple_let_eq pat rhs
        | Zelus.Evarpat id ->
            let x = Zident.name id in
            process_scalar_eq base_pat ty_ann_zelus rhs
        | _ ->
            failwith "Unsupported let pattern"
        end
      | _ -> ()
    end
  | _ -> ()

  let with_env_snapshot (f : unit -> unit) : unit =
    let saved = !gamma in
    match f () with
    | () -> gamma := saved
    | exception ex -> gamma := saved; raise ex
  
  
  let check_return ~(fname:string)
                   ~(ret_binder:string)
                   ~(ret_base:string)
                   ~(ret_pred:Zelus.exp)
                   (e:Zelus.exp) : unit =
    (* Build LHS singleton from the *return expression* e with base = ret_base. *)
    let lhs =
      singleton_type_of_const
        { desc = vc_gen_expression e; loc = dummy_loc }
        ret_base
    in
    (* Build RHS from the declared return refinement; ensure binder consistency. *)
    let rhs =
      mk_type (Zparsetree.Erefinement
                 ((ret_binder,
                   mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii ret_base), []))),
                  { desc = vc_gen_expression ret_pred; loc = dummy_loc }))
    in
    if not (run_fq fname lhs rhs) then
      failwith (Printf.sprintf "Liquid type error: %s does not satisfy its annotation" fname)
  
  let rec check_fun_body ~(fname:string)
                         ~(ret_binder:string)
                         ~(ret_base:string)
                         ~(ret_pred:Zelus.exp)
                         (e:Zelus.exp) : unit =
    match e.e_desc with
    | Zelus.Elet (l_block, r_exp) ->
        (* New scope for this let: bindings only live inside r_exp. *)
        with_env_snapshot (fun () ->
          (* handle “let ... and ... and ...” *)
          List.iter process_let_eq l_block.l_eq;
          (* continue into the body; handles further nested lets too *)
          check_fun_body ~fname ~ret_binder ~ret_base ~ret_pred r_exp
        )
  
    | Zelus.Eseq (e1, e2) ->
        let rec process_lets_only (e:Zelus.exp) =
          match e.e_desc with
          | Zelus.Elet (l_block, r_exp) ->
              with_env_snapshot (fun () ->
                List.iter process_let_eq l_block.l_eq;
                process_lets_only r_exp)
          | Zelus.Eseq (a,b) -> process_lets_only a; process_lets_only b
          | _ -> ()
        in
        process_lets_only e1;
        check_fun_body ~fname ~ret_binder ~ret_base ~ret_pred e2

  
    | _ ->
        check_return ~fname ~ret_binder ~ret_base ~ret_pred e
  
  
      
let rec implementation (impl : Zelus.implementation_desc Zelus.localized) =
  match impl.desc with
  | Zelus.Econstdecl (id, rhs_ty, _is_static, e) -> (
    match e.e_desc with
      | Zelus.Eop(Eifthenelse,i::t::el::[]) -> 
        debug (Printf.sprintf "id %s ifthenelse" id);
        (match rhs_ty.desc with 
        | Zelus.Erefinement((v,base_ty), pred) -> 
          (match base_ty.desc with 
            | Zelus.Etypeconstr(Name base, []) -> process_ite id v base pred.e_desc e
            | _ -> failwith (Printf.sprintf "Not a Etypeconstr"))
        | _ -> failwith (Printf.sprintf "Not a refinement"))
      | _ -> 
        (debug (Printf.sprintf "id %s" id);
        match rhs_ty.desc with
        | Zelus.Erefinement((v, base_ty), pred) ->
          (
          match base_ty.desc with 
            | Zelus.Etypefun(a, b, arg, out) -> (
              match arg.desc with
              | Zelus.Etypeconstr(Name base, []) -> (
                match out.desc with
                  |Zelus.Etypeconstr(Name base_out, []) -> (
                    match pred.e_desc with
                    (* | Zelus.Eapp({ app_inline = bool1; app_statefull = bool2 },
                    { e_desc = Zelus.Eglobal{lname = (Name op)}; _ },
                    list) -> process_eapp ~name:id ~v ~base:base ~op list  ~e
                    | Zelus.Eop(_,_) -> failwith (Printf.sprintf "Yes it is an Eop") *)
                    (*Liquid fixpoint doesn't allow having {v:Int| c or var} only {v:base| true or false} that's why I commented out the following predicate matchings*)
                    (* | Zelus.Elocal{num = i; source = n} -> failwith (Printf.sprintf "Yes it is an Elocal")
                    | Zelus.Eglobal{lname = Modname qualid} -> failwith (Printf.sprintf "Yes it is an Eglobal modname") *)
                    (* | Zelus.Eglobal{lname = Name var} -> process_global id v base var e *)
                    | Zelus.Eglobal(_)-> process_bool_fun id v base base_out pred.e_desc e (to_zpt_kind a) (zident_opt_to_string_opt b) 
                    | Zelus.Econst(Ebool(_)) -> process_bool_fun id v base base_out pred.e_desc e (to_zpt_kind a) (zident_opt_to_string_opt b) 
                    | _ -> failwith (Printf.sprintf "Not an Eapp"))
              | _ -> failwith (Printf.sprintf "Not handling function types for now")))
            | Zelus.Etypeconstr(Name base, []) ->
              match pred.e_desc with
                | Zelus.Eapp({ app_inline = bool1; app_statefull = bool2 },
                { e_desc = Zelus.Eglobal{lname = (Name op)}; _ },
                list) -> process_and_run ~name:id ~v ~base:base ~op list  ~e
                | Zelus.Eop(op,exp_list) -> (
                  match op with 
                    | Zelus.Eifthenelse -> failwith (Printf.sprintf "Not handling ifthenelse for now")
                    | _ -> failwith (Printf.sprintf "Not handling this Eop for now")
                )
                (*Liquid fixpoint doesn't allow having {v:Int| c or var} only {v:base| true or false} that's why I commented out the following predicate matchings*)
                (* | Zelus.Elocal{num = i; source = n} -> failwith (Printf.sprintf "Yes it is an Elocal")
                | Zelus.Eglobal{lname = Modname qualid} -> failwith (Printf.sprintf "Yes it is an Eglobal modname") *)
                (* | Zelus.Eglobal{lname = Name var} -> process_global id v base var e *)
                | Zelus.Eglobal(_)-> process_bool id v base pred.e_desc e
                | Zelus.Econst(Ebool(_)) -> process_bool id v base pred.e_desc e
                | _ -> failwith (Printf.sprintf "Not an Eapp")
            | _ -> failwith (Printf.sprintf "Not an Etypeconstr"))
        | Etypetuple(_) -> failwith (Printf.sprintf "Not handling Etypetuple for now")
        | Erefinementlabeledtuple((x::xs, pred)) -> failwith (Printf.sprintf "Not handling Erefinementlabeledtuple for now")
        | _ ->
            failwith (Printf.sprintf "Not a refinement type")
        ))
  | Efundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
      f_body = f_body; f_loc = loc; f_retrefine = rettype }) -> debug(Printf.sprintf "Efundecl %s\n" n);
      debug(Printf.sprintf "# of Arguments: %d\n" (List.length p_list));
    debug(Printf.sprintf "Argument------: \n" );
      if n = "main" then (
        debug (Printf.sprintf "skipping main function for now, fix this bug");
      ) else (
        let (ret_pred_exp, var_req, ret_base_ty) =
        match rettype.desc with
        | Zelus.Erefinement ((n,t), exp) -> (exp, n, t)
        | Zelus.Erefinementlabeledtuple (t_list, e) ->
            (debug "Ignoring tuple returns for now";
             (e, (fst (List.hd t_list)), (snd (List.hd t_list))))
        | _ -> failwith "Not a refinement type in the return type"
      in
      let base =
        match ret_base_ty.desc with
        | Zelus.Etypeconstr (Name base, []) -> base
        | _ -> failwith "Return base is not an Etypeconstr(Name,[])"
      in

      check_fun_body n var_req base ret_pred_exp f_body
      )
  | _ ->
      failwith (Printf.sprintf "Not a Econstdcl")


let implementation_list ff (impl_list: Zelus.implementation_desc Zelus.localized list) : Zelus.implementation_desc Zelus.localized list  =
  List.iter implementation impl_list;
  impl_list