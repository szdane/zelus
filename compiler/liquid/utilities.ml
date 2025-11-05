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
let mk_app f args     = { desc = Zparsetree.Eapp ({app_inline=false; app_statefull=false}, f, args); loc = dummy_loc }
let mk_var s          = { desc = Zparsetree.Evar (Name s); loc = dummy_loc }
let mk_and a b = mk_app (mk_var "&&") [a; b]
let mk_paren (e : Zparsetree.exp) : Zparsetree.exp =
  { desc =
      Zparsetree.Eapp (
        { app_inline = true; app_statefull = false },
        { desc = Zparsetree.Evar (Name ""); loc = dummy_loc },
        [ e ]
      );
    loc = dummy_loc
  }
let mk_eq a b         = mk_app (mk_var "=")  [a; b]
let mk_true : Zparsetree.exp =
  { desc = Zparsetree.Econst (Ebool true); loc = dummy_loc }
let mk_X  e = mk_app (mk_var "x") [e]
let mk_G e =
  { desc = Zparsetree.Eapp ({app_inline=false; app_statefull=false},
                            {desc = Zparsetree.Evar (Name "g"); loc = dummy_loc},
                            [e]);
    loc = dummy_loc }

let mk_M e =
  { desc = Zparsetree.Eapp ({app_inline=false; app_statefull=false},
                            {desc = Zparsetree.Evar (Name "m"); loc = dummy_loc},
                            [e]);
    loc = dummy_loc }
let mk_v () =
  { desc = Zparsetree.Evar (Name "v"); loc = dummy_loc }
let strip_once (fname:string) (base:string) (e:Zparsetree.exp) : Zparsetree.exp option =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name f); _ }, [arg])
      when String.equal f fname -> Some arg
  | _ -> None

let rec strip_temporal_chain (base:string) (e:Zparsetree.exp) : Zparsetree.exp =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name f); _ }, [arg]) ->
      if String.equal f "x"
          || String.equal f "g"
          || String.equal f "m"
      then strip_temporal_chain base arg
      else e
  | _ -> e

  


let decompose_fby_goal (base:string) (pred:Zparsetree.exp)
  : (Zparsetree.exp * Zparsetree.exp) option =
  let is_and = function
    | { desc = Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "&&"); _}, [_;_]); _ } -> true
    | _ -> false
  in
  let as_pair = function
    | { desc = Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "&&"); _}, [p1;p2]); _ } -> Some (p1,p2)
    | _ -> None
  in
  match as_pair pred with
  | None -> None
  | Some (p,q) ->
      let try_order a b =
        let psi_raw =  strip_temporal_chain base b in
        Some (a, psi_raw)
      in
      match try_order p q with
      | Some x -> Some x
      | None ->
          try_order q p

let e_true : Zparsetree.exp =
  { desc = Zparsetree.Econst (Ebool true); loc = dummy_loc }

(* Detect if an expression is headed by a temporal operator we care about *)
let is_temporal_head (e:Zparsetree.exp) : bool =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name f); _ }, _args) ->
      (* extend this set if you add more temporal uifs *)
      f = "X" || f = "G" || f = "M"
      || f = "x" || f = "g" || f = "m"
  | _ -> false

(* Try to extract an equality atom of the shape (binder = rhs) from a ZPT expr.
    Returns SOME(binder = rhs) if found at top-level or as (some) subexpr;
    otherwise NONE.  This keeps it lightweight: it only looks at the top-level
    and under a single G/X/F/M application (common in your use-cases). *)
let rec find_eq_atom_for_binder (binder:string) (e:Zparsetree.exp)
  : Zparsetree.exp option =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "="); _ }, [lhs; rhs]) ->
      (match lhs.desc with
        | Zparsetree.Evar (Name v) when String.equal v binder ->
            Some (mk_eq lhs rhs)
        | _ -> None)

  (* Peel one temporal layer and look again (e.g., G(v=5) -> find v=5) *)
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name f); _ }, [arg])
      when f="G" || f="X" || f="M" || f="g" || f="x" || f="m" ->
      find_eq_atom_for_binder binder arg

  | _ -> None


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


let gensym =
  let c = ref 0 in
  fun (p:string) -> incr c; Printf.sprintf "%s_%d" p !c
let is_var = function
  | { desc = Zparsetree.Evar (Name _); _ } -> true
  | _ -> false

let starts_with s ~prefix =
  let n = String.length prefix in
  String.length s >= n && String.sub s 0 n = prefix
  
let t_hd base t = mk_app (mk_var "hd") [t]
let t_G  base t = mk_app (mk_var "g") [t]
let t_X  base t = mk_app (mk_var "x") [t]
let t_M  base t = mk_app (mk_var "m") [t] 

let add_bool_ghost (gname:string) phi  =
  let v   = { desc = Zparsetree.Evar (Name "v"); loc = dummy_loc } in
  let eq  = mk_eq v (mk_paren phi) in
  let bty = { desc = Zparsetree.Etypeconstr (Name "bool", []); loc = dummy_loc } in
  let ty  = { desc = Zparsetree.Erefinement (("v", bty), eq); loc = dummy_loc } in
  add_binding gname ty;
  ty


let is_temporal_head (e:Zparsetree.exp) : bool =
  match e.desc with
  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name f); _}, _)
      when f = "x" || f = "g" || f = "m" -> true
  | _ -> false