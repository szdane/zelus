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
      f = "X" || f = "G" || f = "M"
      || f = "x" || f = "g" || f = "m"
  | _ -> false

let rec find_eq_atom_for_binder (binder:string) (e:Zparsetree.exp)
  : Zparsetree.exp option =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "="); _ }, [lhs; rhs]) ->
      (match lhs.desc with
        | Zparsetree.Evar (Name v) when String.equal v binder ->
            Some (mk_eq lhs rhs)
        | _ -> None)

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
let add_binding_sim name ty = 
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
  let eq  = mk_true in
  let bty = { desc = Zparsetree.Etypeconstr (Name "bool", []); loc = dummy_loc } in
  let ty  = { desc = Zparsetree.Erefinement (("v", bty), eq); loc = dummy_loc } in
  add_binding_sim gname ty;
  ty


let is_temporal_head (e:Zparsetree.exp) : bool =
  match e.desc with
  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name f); _}, _)
      when f = "x" || f = "g" || f = "m" -> true
  | _ -> false


  let is_named (s:string) (e:Zparsetree.exp) =
    match e.desc with
    | Zparsetree.Evar (Name t) -> String.equal s t
    | _ -> false
  
let rec is_true (e:Zparsetree.exp) : bool =
  match e.desc with
  | Zparsetree.Econst (Ebool true) -> true
  | Zparsetree.Eapp (_, {desc=Zparsetree.Evar (Name "id")}, [arg]) -> is_true arg
  | _ -> false

  
  let view_and (e:Zparsetree.exp) : (Zparsetree.exp * Zparsetree.exp) option =
    match e.desc with
    | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "&&"); _}, [a;b]) -> Some (a,b)
    | _ -> None
  
  let view_unary_app_name (e:Zparsetree.exp) : (string * Zparsetree.exp) option =
    match e.desc with
    | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name f); _}, [arg]) -> Some (f,arg)
    | _ -> None
  
  (* ---------- LTL ops: we now only use plain "x", "g", "m" ---------- *)
  
  type ltl_op = OP_X | OP_G | OP_M
  
  let view_ltl (e:Zparsetree.exp) : (ltl_op * Zparsetree.exp) option =
    match view_unary_app_name e with
    | Some ("x", arg) -> Some (OP_X, arg)
    | Some ("g", arg) -> Some (OP_G, arg)
    | Some ("m", arg) -> Some (OP_M, arg)
    | _               -> None
  
  (* ---------- split NF: φ && x(ψ), default ψ = true if absent ---------- *)
  
  let split_nf (p:Zparsetree.exp) : Zparsetree.exp * Zparsetree.exp =
    match view_and p with
    | Some (phi, xpsi) -> (
        match view_ltl xpsi with
        | Some (OP_X, psi) -> (phi, psi)
        | _ -> (p, mk_true)
      )
    | None -> (p, mk_true)
  
  (* ---------- strip common LTL operator chains from the later part ---------- *)
  
  let rec strip_matching_ltl (a:Zparsetree.exp) (b:Zparsetree.exp)
    : Zparsetree.exp * Zparsetree.exp =
    debug "I'm inside the ltl matching func";
    match view_ltl a, view_ltl b with
    | Some (op1, a1), Some (op2, b1) -> if op1 = op2 then
        strip_matching_ltl a1 b1 else failwith "no matching between LTL"
    | _ -> (a, b)
  
  (* ---------- “LTL-free” = no head x/g/m, and any && parts are LTL-free ---------- *)
  
  let rec is_ltl_free (e:Zparsetree.exp) : bool =
    match view_ltl e with
    | Some _ -> false
    | None ->
        (match view_and e with
         | Some (a,b) -> is_ltl_free a && is_ltl_free b
         | None -> true)
  
  (* ---------- build {v:Base | pred} and run subtyping on predicates ---------- *)
  
  let mk_refine (binder:string) (base:string) (pred:Zparsetree.exp)
    : Zparsetree.type_expression =
    let base_ty =
      mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []))
    in
    mk_type (Zparsetree.Erefinement ((binder, base_ty), pred))


(* --- HOIST NON-VAR BOOLEANS FROM UNDER TEMPORAL OPS INTO GHOSTS --- *)

let is_temporal_op (s:string) = (s = "x" || s = "g" || s = "m" || s = "hd")

(* Replace any non-variable arg under x/g/m/hd with a fresh bool ghost.
   Accumulates (ghost_name, original_arg_expr) pairs. *)
let normalize_pred_for_fixpoint ~(binder:string) (p:Zparsetree.exp)
: Zparsetree.exp =
    let ghosts : (string * Zparsetree.exp) list ref = ref [] in

    (* Insert a ghost for [a] if it's not a var or bare bool. *)
    let hoist_arg_if_needed (a:Zparsetree.exp) : Zparsetree.exp =
      match a.desc with
      | Zparsetree.Evar (Name _) -> a
      | Zparsetree.Econst (Ebool _) -> a
      | _ ->
          let g = gensym "tmp" in
          ghosts := (g, a) :: !ghosts;
          (* Register ghost in Γ as {g:bool | g = a} *)
          let ty1 = add_bool_ghost g a in 
          mk_var g
    in
 
   (* Recurse, preserving temporal structure; only hoist the *argument* of temporal ops. *)
  let rec norm (e:Zparsetree.exp) : Zparsetree.exp =
    match e.desc with
    (* Temporal head with one argument: normalize the argument; then hoist if needed. *)
    | Zparsetree.Eapp (cfg, { desc = Zparsetree.Evar (Name op); _ }, [arg])
        when is_temporal_op op ->
        let arg_norm = norm arg in
        let arg_final =
          match arg_norm.desc with
          | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name op2); _ }, _)
              when is_temporal_op op2 ->
              (* Argument is itself temporal — keep it; do NOT hoist the temporal node. *)
              arg_norm
          | _ ->
              (* Argument is non-temporal: hoist to a ghost if not var/bool. *)
              hoist_arg_if_needed arg_norm
        in
        { desc = Zparsetree.Eapp (cfg, { desc = Zparsetree.Evar (Name op); loc = dummy_loc }, [arg_final]);
          loc  = dummy_loc }

    (* General application: normalize subexpressions. *)
    | Zparsetree.Eapp (cfg, f, args) ->
        { desc = Zparsetree.Eapp (cfg, f, List.map norm args);
          loc  = dummy_loc }

    (* Tuples: normalize components. *)
    | Zparsetree.Etuple es ->
        { desc = Zparsetree.Etuple (List.map norm es);
          loc  = dummy_loc }

    (* Everything else unchanged. *)
    | _ -> e
  in
 
   let p' = norm p in
 
   (* Conjoin ghost definitions up front: (g1 = e1) && (g2 = e2) && ... && p' *)
  let defs =
    List.map (fun (g, e) -> mk_paren(mk_eq (mk_var g) (mk_paren e))) !ghosts
  in
  List.fold_left (fun acc d -> mk_and d acc) p' defs


let add_binding (name:string) (ty:Zparsetree.type_expression) =
  match ty.desc with
  | Erefinement ((var, base_ty), lpred) ->
      (* Normalize predicate so LF sees only vars under temporal ops *)
      let lpred_norm = normalize_pred_for_fixpoint ~binder:name lpred in
      let ty' =
        { desc = Erefinement ((name, base_ty), lpred_norm);
          loc  = dummy_loc }
      in
      gamma := Env.add name ty' !gamma
  | _ ->
      failwith "add_binding: expected a refinement type"

let pp_nf_as_type ~(binder:string) ~(base:string) (nf:Zparsetree.exp) : string =
  let ty =
    { desc = Zparsetree.Erefinement
              ((binder,
                { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []); loc = dummy_loc }),
                nf);
      loc = dummy_loc }
  in
  Pprint.string_of_type ty


(* Build ZPT guard from a Zelus condition *)



