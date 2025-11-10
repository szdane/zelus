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
let mk_not (p : Zparsetree.exp) : Zparsetree.exp =
  mk_app (mk_var "not") [p]

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
let gamma1 : type_expression Env.t ref = ref Env.empty
let add_binding_sim name ty = 
  match ty.desc with
    | Erefinement((var, base_ty), lpred) -> 
    gamma := Env.add name ({desc = Erefinement((name, base_ty), lpred); loc = dummy_loc}) !gamma;
    gamma1 := Env.add name ({desc = Erefinement((name, base_ty), lpred); loc = dummy_loc}) !gamma1;
    | _ -> failwith(Printf.sprintf "It's not a refinement type")
let current_env ()      = !gamma |> Env.bindings |> List.map snd


let gensym =
  let c = ref 0 in
  fun (p:string) -> incr c; Printf.sprintf "%s_%d" p !c
let is_var = function
  | { desc = Zparsetree.Evar (Name _); _ } -> true
  | _ -> false

  
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
    | Some (op1, a1), Some (op2, b1) -> if (op1 = op2 || op1 == OP_G) then
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
      let ty =
        { desc = Erefinement ((name, base_ty), lpred);
          loc  = dummy_loc }
      in
      gamma := Env.add name ty' !gamma;
      gamma1 := Env.add name ty !gamma1;
  | _ ->
      failwith "add_binding: expected a refinement type"

let add_binding_for_tuples (name:string) (ty:Zparsetree.type_expression) =
    match ty.desc with
    | Zparsetree.Erefinement ((var, base_ty), lpred) ->
    let lpred_norm = normalize_pred_for_fixpoint ~binder:var lpred in
    let ty' =
    { desc = Zparsetree.Erefinement ((var, base_ty), lpred_norm)
    ; loc  = ty.loc
    }
    in
    gamma := Env.add name ty' !gamma
    | _ ->
    (* Non-refinement – just drop in. *)
    gamma := Env.add name ty !gamma


let pp_nf_as_type ~(binder:string) ~(base:string) (nf:Zparsetree.exp) : string =
  let ty =
    { desc = Zparsetree.Erefinement
              ((binder,
                { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []); loc = dummy_loc }),
                nf);
      loc = dummy_loc }
  in
  Pprint.string_of_type ty

(* Build a ZPT base type like Int/Bool/Real from a base name. *)
let zpt_base (b : string) : Zparsetree.type_expression =
  mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii b), []))

(* Extract (binder_name, base_name) for one argument pattern+type.
   We only rely on an *explicit* annotation on the arg (like (x : {v:Int|...}) or (x:Int)).
   If there is no explicit base in the arg annotation, we fail (keeps behavior simple/back-compatible). *)
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
let rec zelus_var_name_of_pat (p : Zelus.pattern) : string =
    match p.p_desc with
    | Zelus.Evarpat id -> zident_pretty id
    | Zelus.Ealiaspat (p', _) -> zelus_var_name_of_pat p'
    | Zelus.Etypeconstraintpat (p', _) -> zelus_var_name_of_pat p'
    | _ -> failwith "Tuple let: component must be a variable (optionally aliased/annotated)"
let arg_binder_and_base (p : Zelus.pattern) : (string * string) =
  match p.p_desc with
  | Zelus.Etypeconstraintpat (p', ann_ty) ->
      let x = zelus_var_name_of_pat p' in
      let base_name =
        match ann_ty.desc with
        | Zelus.Erefinement ((_v, base_ty), _pred) ->
            (match base_ty.desc with
             | Zelus.Etypeconstr (Name b, []) -> b
             | _ -> failwith "Function arg base must be Etypeconstr(Name,[])")
        | Zelus.Etypeconstr (Name b, []) -> b
        | _ -> failwith "Function arg type must be a base or base refinement"
      in
      (x, base_name)
  | Zelus.Evarpat _ ->
      failwith "Function argument lacks an explicit type annotation"
  | _ ->
      failwith "Unsupported function argument pattern (tuples/aliases not yet supported)"

(* Given the arg list and a return base, build a curried Etypefun chain:
     τ1 -> τ2 -> ... -> τn -> τret
   so that Pprint prints it as func(n,[τ1,...,τn,τret]). *)
let rec mk_fun_sort_from_args
  (k : Zelus.kind) (args : Zelus.pattern list) (ret_base : string)
  : Zparsetree.type_expression =
  match args with
  | [] -> zpt_base ret_base
  | p::ps ->
      let (_x, b) = arg_binder_and_base p in
      mk_type (Zparsetree.Etypefun (to_zpt_kind k, None,
                                    zpt_base b,
                                    mk_fun_sort_from_args k ps ret_base))

                                   
let map_find_opt k m =
  try Some (Env.find k m) with Not_found -> None

(* 3) Lookup previously-installed binding from Γ *)
let find_binding (x : string) : Zparsetree.type_expression option =
  map_find_opt x !gamma1

let rec subst_binder_in_pred (oldb:string) (newb:string) (p:Zparsetree.exp) : Zparsetree.exp =
  let recur = subst_binder_in_pred oldb newb in
  match p.desc with
  | Zparsetree.Evar (Name s) when s = oldb ->
      { p with desc = Zparsetree.Evar (Name newb) }
  | Zparsetree.Eapp (ai, f, args) ->
      { p with desc = Zparsetree.Eapp (ai, f, List.map recur args) }
  | Zparsetree.Etuple es ->
      { p with desc = Zparsetree.Etuple (List.map recur es) }
  | Zparsetree.Econst _
  | _ -> p

let rec rename_var_in_exp (oldv:string) (newv:string) (e:Zparsetree.exp) : Zparsetree.exp =
  let loc = e.loc in
  let rec go e =
    match e.desc with
    | Zparsetree.Evar (Name s) when s = oldv ->
        { desc = Zparsetree.Evar (Name newv); loc }
    | Zparsetree.Eapp (ai, f, args) ->
        { desc = Zparsetree.Eapp (ai, go f, List.map go args); loc }
    | Zparsetree.Etuple es ->
        { desc = Zparsetree.Etuple (List.map go es); loc }
    | _ -> e
  in
  go e



(* ---------- canon_from_env: turn stored (Fixpoint-friendly) types into Marvelus NF ---------- *)

(* flatten conjunctions a && b regardless of nesting *)
let rec flatten_and (e:Zparsetree.exp) : Zparsetree.exp list =
  match e.desc with
  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "&&"); _}, [a; b]) ->
      (flatten_and a) @ (flatten_and b)
  | _ -> [e]

let mk_and2 a b =
  match a.desc, b.desc with
  | Zparsetree.Econst (Ebool true), _ -> b
  | _, Zparsetree.Econst (Ebool true) -> a
  | _ ->
    { desc = Zparsetree.Eapp ({app_inline=false; app_statefull=false},
                               {desc=Zparsetree.Evar (Name "&&"); loc=dummy_loc},
                               [a;b]); loc = dummy_loc }

let conj_list = function
  | []    -> mk_true
  | x::xs -> List.fold_left mk_and2 x xs

(* detect equations of the form: tmp = φ, returning (Some (tmp, φ)) *)
let eq_tmp_binding (e:Zparsetree.exp) : (string * Zparsetree.exp) option =
  match e.desc with
  | Zparsetree.Eapp (_,
      {desc = Zparsetree.Evar (Name "="); _},
      [{desc = Zparsetree.Evar (Name tmp); _}; phi]) ->
      (* heuristically treat names starting with "tmp_" or "hd_" as witnesses; or accept any bool var *)
      Some (tmp, phi)
  | _ -> None

(* substitute occurrences of a variable name with an expression *)
let rec subst_var (vname:string) (repl:Zparsetree.exp) (e:Zparsetree.exp) : Zparsetree.exp =
  match e.desc with
  | Zparsetree.Evar (Name n) when n = vname -> repl
  | Zparsetree.Eapp (ai, f, args) ->
      { e with desc = Zparsetree.Eapp (ai, f, List.map (subst_var vname repl) args) }
  | Zparsetree.Etuple es ->
      { e with desc = Zparsetree.Etuple (List.map (subst_var vname repl) es) }
  | _ -> e

(* inline all boolean witness bindings tmp = φ, and drop those equalities *)
let inline_witness_bools (pred:Zparsetree.exp) : Zparsetree.exp =
  let parts = flatten_and pred in
  let (bindings, others) =
    List.fold_right
      (fun c (bs, os) ->
        match eq_tmp_binding c with
        | Some (tmp, phi) -> ((tmp, phi)::bs, os)
        | None            -> (bs, c::os))
      parts ([], [])
  in
  (* apply substitutions in the remaining conjuncts *)
  let substituted =
    List.fold_left
      (fun acc (v,phi) -> List.map (subst_var v phi) acc)
      others
      bindings
  in
  conj_list substituted

let rec expr_mentions (x : string) (e : Zelus.exp) : bool =
  let rec go e =
    match e.e_desc with
    | Zelus.Elocal { source = y; _ } -> String.equal x y
    | Zelus.Eglobal { lname = Name y } -> String.equal x y
    | Zelus.Eglobal _ -> false
    | Zelus.Etuple es -> List.exists go es
    | Zelus.Eapp (_, f, args) -> go f || List.exists go args
    | Zelus.Eop (_, es) -> List.exists go es
    | Zelus.Eblock _ -> false
    | Zelus.Econst _ -> false
    | Zelus.Elet (lb, body) ->
        List.exists (fun eq -> (* be conservative: scan rhs of eqs *) 
          match eq.eq_desc with
          | EQeq (_, rhs) -> go rhs
          | _ -> false) lb.l_eq
        || go body
    | Zelus.Eseq (e1,e2) -> go e1 || go e2
    | _ -> false
  in
  go e

let expr_mentions_any (xs : string list) (e : Zelus.exp) : bool =
  List.exists (fun x -> expr_mentions x e) xs

let rec subst_var_in_zpt_exp ~(old_nm:string) ~(new_nm:string)
   (e:Zparsetree.exp) : Zparsetree.exp =
 let loc = e.loc in
 match e.desc with
 | Zparsetree.Evar (Name nm) when nm = old_nm ->
     { desc = Zparsetree.Evar (Name new_nm); loc }

 | Zparsetree.Eapp (ai, f, args) ->
     { desc = Zparsetree.Eapp (ai,
             subst_var_in_zpt_exp ~old_nm ~new_nm f,
             List.map (subst_var_in_zpt_exp ~old_nm ~new_nm) args);
       loc }

 | Zparsetree.Etuple es ->
     { desc = Zparsetree.Etuple (List.map (subst_var_in_zpt_exp ~old_nm ~new_nm) es); loc }

 | _ -> e

 let rec zpt_subst_names (e : Zparsetree.exp)
                        (f : string -> string option) : Zparsetree.exp =
  let open Zparsetree in
  let recur x = zpt_subst_names x f in
  match e.desc with
  | Evar (Name s) ->
      (match f s with
       | Some s' -> { e with desc = Evar (Name s') }
       | None    -> e)
  | Eapp (ai, fn, args) ->
      { e with desc = Eapp (ai, recur fn, List.map recur args) }
  | Etuple es ->
      { e with desc = Etuple (List.map recur es) }
  | _ -> e

and zpt_subst_type (t : Zparsetree.type_expression)
                   (f : string -> string option) : Zparsetree.type_expression =
  let open Zparsetree in
  match t.desc with
  | Etypeconstr _ -> t
  | Etypetuple ts ->
      { t with desc = Etypetuple (List.map (fun tt -> zpt_subst_type tt f) ts) }
  | Etypefun (k, zopt, a, b) ->
      { t with desc = Etypefun (k, zopt, zpt_subst_type a f, zpt_subst_type b f) }
  | Erefinement ((b, base), p) ->
      { t with desc = Erefinement ((b, zpt_subst_type base f), zpt_subst_names p f) }
  | Erefinementlabeledtuple (fields, p) ->
      let fields' = List.map (fun (nm, ty) -> (nm, zpt_subst_type ty f)) fields in
      { t with desc = Erefinementlabeledtuple (fields', zpt_subst_names p f) }
  | _ -> t

let singleton_eq_zpt ~(binder:string) ~(base:string) ~(rhs:Zparsetree.exp)
  : Zparsetree.type_expression =
  let open Zparsetree in
  let base_ty =
    { loc = dummy_loc; desc = Etypeconstr (Name (String.lowercase_ascii base), []) }
  in
  let v    = { loc = dummy_loc; desc = Evar (Name binder) } in
  let eq   = { loc = dummy_loc; desc = Evar (Name "=") } in
  let pred = { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, eq, [v; rhs]) } in
  { loc = dummy_loc; desc = Erefinement ((binder, base_ty), pred) }

let nf_eq_v_rhs_fby_tail_zpt (rhs : Zparsetree.exp) : Zparsetree.exp =
  let open Zparsetree in
  let v    = { loc = dummy_loc; desc = Evar (Name "v") } in
  let eq   = { loc = dummy_loc; desc = Evar (Name "=") } in
  let v_eq = { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, eq, [v; rhs]) } in
  let m    = { loc = dummy_loc; desc = Evar (Name "m") } in
  let g    = { loc = dummy_loc; desc = Evar (Name "g") } in
  let x    = { loc = dummy_loc; desc = Evar (Name "x") } in
  let m_v  = { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, m, [v_eq]) } in
  let g_m  = { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, g, [m_v]) } in
  let x_gm = { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, x, [g_m]) } in
  (* v=rhs ∧ X(G(M(v=rhs))) *)
  let and_ = { loc = dummy_loc; desc = Evar (Name "&&") } in
  { loc = dummy_loc; desc = Eapp ({app_inline=false; app_statefull=false}, and_, [v_eq; x_gm]) }

let phi_now_for_tj ~(phi_now:Zparsetree.exp)
                   ~(bvars:string list)
                   ~(t_names:string list)
                   ~(j:int)
  : Zparsetree.exp =
  let f name =
    (* if name is v_i *)
    match List.find_opt (fun vi -> vi = name) bvars with
    | None -> None
    | Some vi ->
        let i = List.find_index (fun s -> s = vi) bvars in
        match i with 
        | Some(im) ->
        if (im= j) then Some "v"                       (* v_j -> binder v *)
        else Some (List.nth t_names im)               (* v_i -> t_i    *)
  in
  zpt_subst_names phi_now f

let subst_xs_to_ts ~(rhs_zpt:Zparsetree.exp)
                   ~(xs:string list)
                   ~(t_names:string list)
  : Zparsetree.exp =
  let f name =
    match List.find_opt (fun x -> x = name) xs with
    | None -> None
    | Some x ->
        let i = List.find_index (fun s -> s = x) xs in
        match i with 
        | Some(i) ->
        Some (List.nth t_names i)
  in
  zpt_subst_names rhs_zpt f

let find_index_opt (x : string) (xs : string list) : int option =
  let rec go i = function
    | [] -> None
    | y :: ys -> if String.equal x y then Some i else go (i+1) ys
  in
  go 0 xs

let singleton_left_eq_v_zpt ~(left_name:string) ~(base:string)
  : Zparsetree.type_expression =
  let base_ty =
    { Zparsetree.loc = dummy_loc
    ; desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), [])
    }
  in
  let pred =
    mk_eq
      { desc = Zparsetree.Evar (Name left_name); loc = dummy_loc }
      (mk_v ())
  in
  { Zparsetree.loc = dummy_loc
  ; desc = Zparsetree.Erefinement (("v", base_ty), pred)
  }
  (* Add explicit parentheses where needed so printing preserves grouping *)
let rec paren_for_prec (e : Zparsetree.exp) : Zparsetree.exp =
  let wrap_if_sum (x : Zparsetree.exp) : Zparsetree.exp =
    match x.desc with
    | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name op); _ }, _)
      when op = "+" || op = "-" ->
        mk_paren x
    | _ -> x
  in
  match e.desc with
  | Zparsetree.Eapp (f, ({ desc = Zparsetree.Evar (Name "*"); _ } as op), [a; b]) ->
      let a' = paren_for_prec a |> wrap_if_sum in
      let b' = paren_for_prec b |> wrap_if_sum in
      { e with desc = Zparsetree.Eapp (f, op, [a'; b']) }

  (* Recurse generically for other apps *)
  | Zparsetree.Eapp (f, op, args) ->
      { e with desc = Zparsetree.Eapp (f, op, List.map paren_for_prec args) }

  (* Keep traversing tuples too, just in case *)
  | Zparsetree.Etuple es ->
      { e with desc = Zparsetree.Etuple (List.map paren_for_prec es) }

  | _ -> e
