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
let mk_or p q = mk_app (mk_var "||") [p; q]
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
let mk_X  e = mk_app (mk_var "nxt") [e]
let mk_G e =
  { desc = Zparsetree.Eapp ({app_inline=false; app_statefull=false},
                            {desc = Zparsetree.Evar (Name "globally"); loc = dummy_loc},
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

let mk_le a b =  mk_app (mk_var "<") [a;b]
let mk_ge a b = mk_app (mk_var ">") [a;b]


let mk_false : Zparsetree.exp =
  { desc = Zparsetree.Econst (Ebool false); loc = dummy_loc }

let mk_or a b =
  mk_app (mk_var "||") [a; b]

let mk_big_and (es:Zparsetree.exp list) : Zparsetree.exp =
  match es with
  | [] -> mk_true
  | e::tl -> List.fold_left mk_and e tl

let mk_big_or (es:Zparsetree.exp list) : Zparsetree.exp =
  match es with
  | [] -> mk_false
  | e::tl -> List.fold_left mk_or e tl

let vars_of_refenv = function
  | None -> []
  | Some re ->
      match re.desc with
      | Erefenv xs -> xs

let plain_state_handlers (handlers_ann : state_handler_ann list)=
  List.map (fun sha -> sha.sha_handler) handlers_ann

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

let literal_and_base = function
  | Deftypes.Eint  n  -> Zparsetree.Eint n  , "Int"
  | Deftypes.Efloat f -> Zparsetree.Efloat f, "Real"
  | Ebool b  -> Zparsetree.Ebool b, "Bool"
  | Estring s -> Zparsetree.Estring s , "String"
  | _         -> failwith "Unsupported literal in Liquid prototype"

let as_desugared_reset_block e_desc : (Zelus.exp * Zelus.exp) option =
    match e_desc with
    | Zelus.Eblock (blk, result_exp) ->
        begin match blk.b_body, result_exp.e_desc with
        | [eq_reset], Zelus.Elocal { source = result_name; _ } ->
            begin match eq_reset.eq_desc with
            | Zelus.EQreset ([eq_inner], cond) ->
                begin match eq_inner.eq_desc with
                | Zelus.EQeq (pat, inner_e) ->
                    begin match pat.p_desc with
                    | Zelus.Evarpat pat_name
                      when String.equal (zident_pretty pat_name) (result_name) ->
                        Some (inner_e, cond)
                    | _ -> None
                    end
                | _ -> None
                end
            | _ -> None
            end
        | _ -> None
        end
    | _ -> None


let add_last_prefix (n:int) (base:string) : string =
  let rec loop acc k =
    if k <= 0 then acc else loop ("last_" ^ acc) (k - 1)
  in
  loop base n

let shifted_var_name ~(extra:int) (base:string) : string =
  add_last_prefix extra base



  let var_name_with_last_depth (base:string) (depth:int) : string =
    let rec aux acc d =
      if d <= 0 then acc else aux ("last_" ^ acc) (d - 1)
    in
    aux base depth
  


let rec vc_gen_expression ({ e_desc = desc; e_loc = loc }) =
  match desc with
  | Zelus.Econst(i) -> Zparsetree.Econst(fst (literal_and_base i))
  | Zelus.Eglobal{lname = Name n} -> Zparsetree.Evar(Name n)
  | Zelus.Eglobal{lname = Modname qualid} -> Zparsetree.Evar(Name qualid.id)
  | Zelus.Elocal{num = i; source = n} -> Zparsetree.Evar(Name n)
  (* | Zelus.Etuple(exp_list) -> Zparsetree.Etuple(List.map (fun exp -> {desc = vc_gen_expression exp; loc = dummy_loc}) exp_list) *)
  | Zelus.Etuple exp_list ->
    Zparsetree.Etuple
      (List.map (fun exp -> { desc = vc_gen_expression exp; loc = dummy_loc }) exp_list)

  (* | Zelus.Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> Zparsetree.Eapp({ app_inline = i; app_statefull = r }, {desc = (vc_gen_expression e); loc = dummy_loc}, vc_gen_exp_list e_list) *)
  | Zelus.Eapp ({ app_inline = i; app_statefull = r }, e, e_list) ->
    Zparsetree.Eapp
      ( { app_inline = i; app_statefull = r }, { desc = vc_gen_expression e; loc = dummy_loc }, List.map (fun exp -> { desc = vc_gen_expression exp; loc = dummy_loc }) e_list )
  | Zelus.Eop(op, exp_list) -> (match op with 
      | Zelus.Eifthenelse -> failwith (Printf.sprintf "Not handling ifthenelse for now")
      | Zelus.Efby -> failwith (Printf.sprintf "Not handling fby for now")
      | _ -> failwith (Printf.sprintf "Not handling this Eop for now")
    )
  | Zelus.Eblock(_) -> begin match as_desugared_reset_block desc with
    | Some (_inner_e, cond) ->
      failwith "vc_gen_expression: encountered desugared reset block; handle through reset NF synthesis"
    | None ->
      failwith "vc_gen_expression: unsupported Eblock"
  end
  (* | Zelus.Elet(_,exp) -> match exp.e_desc with
      | Econst(_) -> implementation {desc = vc_gen_expression exp; loc = dummy_loc}
      | _ -> failwith (Printf.sprintf "Not handling non constant let for now") *)
  | Zelus.Elast(id) -> Zparsetree.Evar(Name ("last_"^(zident_pretty id)))
  | _ -> failwith(Printf.sprintf "Not handling this expression")

let rec vc_gen_expression_shifted ~(shift:int) ({ e_desc = desc; e_loc = loc } : Zelus.exp) =
    match desc with
    | Zelus.Econst i ->
        Zparsetree.Econst (fst (literal_and_base i))
  
    | Zelus.Eglobal { lname = Name n } ->
        Zparsetree.Evar (Name (var_name_with_last_depth n shift))
  
    | Zelus.Eglobal { lname = Modname qualid } ->
        Zparsetree.Evar (Name (var_name_with_last_depth qualid.id shift))
  
    | Zelus.Elocal { source = n; _ } ->
        Zparsetree.Evar (Name (var_name_with_last_depth n shift))
  
    | Zelus.Elast id ->
        Zparsetree.Evar (Name (var_name_with_last_depth (zident_pretty id) (shift + 1)))
  
    | Zelus.Etuple es ->
        Zparsetree.Etuple
          (List.map (fun e -> { desc = vc_gen_expression_shifted ~shift e; loc = dummy_loc }) es)
  
    | Zelus.Eapp ({ app_inline = i; app_statefull = r }, f, args) ->
        Zparsetree.Eapp
          ( { app_inline = i; app_statefull = r }
          , { desc = vc_gen_expression f; loc = dummy_loc }
          , List.map (fun e -> { desc = vc_gen_expression_shifted ~shift e; loc = dummy_loc }) args )
  
    | Zelus.Eop (op, exp_list) ->
        begin match op with
        | Zelus.Eifthenelse ->
            failwith "vc_gen_expression_shifted: not handling ifthenelse for now"
        | Zelus.Efby ->
            failwith "vc_gen_expression_shifted: nested fby not handled for now"
        | _ ->
            failwith "vc_gen_expression_shifted: not handling this Eop for now"
        end
  
    | _ ->
        failwith "vc_gen_expression_shifted: not handling this expression"
  


let rec strip_temporal_chain (base:string) (e:Zparsetree.exp) : Zparsetree.exp =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name f); _ }, [arg]) ->
      if String.equal f "nxt"
          || String.equal f "globally"
          || String.equal f "m"
      then strip_temporal_chain base arg
      else e
  | _ -> e

let zpt_eq_v_rhs_shifted ~(shift:int) (rhs_zls:Zelus.exp) : Zparsetree.exp =
  mk_eq (mk_v ()) { desc = vc_gen_expression_shifted ~shift rhs_zls; loc = dummy_loc }


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
      f = "nxt" || f = "globally" || f = "m"
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
      when f="globally" || f="nxt" || f="m" ->
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
let t_G  base t = mk_app (mk_var "globally") [t]
let t_X  base t = mk_app (mk_var "nxt") [t]
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
      when f = "nxt" || f = "globally" || f = "m" -> true
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
  let view_unary_app_name_zls (e:Zelus.exp) : (string * Zelus.exp) option =
    match e.e_desc with
    | Zelus.Eapp (_, {e_desc = Zelus.Eglobal {lname = Name f}; _}, [arg]) -> Some (f,arg)
    | Zelus.Eapp (_, {e_desc = Zelus.Elocal {source = f}; _}, [arg]) -> Some (f,arg)
    | _ -> None
  
  
  (* ---------- LTL ops: we now only use plain "nxt", "globally", "m" ---------- *)
  
type ltl_op = OP_X | OP_G | OP_M

let view_ltl (e:Zparsetree.exp) : (ltl_op * Zparsetree.exp) option =
  match view_unary_app_name e with
  | Some ("nxt", arg) -> Some (OP_X, arg)
  | Some ("globally", arg) -> Some (OP_G, arg)
  | Some ("m", arg) -> Some (OP_M, arg)
  | _               -> None

let view_ltl_zls (e:Zelus.exp) : (ltl_op * Zelus.exp) option =
  match view_unary_app_name_zls e with
  | Some ("nxt", arg) -> Some (OP_X, arg)
  | Some ("globally", arg) -> Some (OP_G, arg)
  | Some ("m", arg) -> Some (OP_M, arg)
  | _               -> None


let split_nf (p:Zparsetree.exp) : Zparsetree.exp * Zparsetree.exp =
  match view_and p with
  | Some (phi, xpsi) -> (
      match view_ltl xpsi with
      | Some (OP_X, psi) -> (phi, psi)
      | _ -> (p, mk_true)
    )
  | None -> (p, mk_true)

let step_pred_of_ann_nf (ann_nf : Zparsetree.exp) : Zparsetree.exp =
  let (_phi, later) = split_nf ann_nf in
  match later.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "globally"); _ }, [psi]) ->
      psi
  | Zparsetree.Econst (Ebool true) ->
      mk_true
  | _ ->
      failwith "Expected annotation NF of shape phi && nxt(globally(psi))"

let base_ind_of_nf (nf : Zparsetree.exp) : Zparsetree.exp * Zparsetree.exp =
  let (phi, later) = split_nf nf in
  match later.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "globally"); _ }, [psi]) ->
      (phi, psi)
  | Zparsetree.Econst (Ebool true) -> (phi, mk_true)
  | _ ->
      failwith "base_ind_of_nf: expected phi && nxt(globally(psi))"
  
  (* ---------- strip common LTL operator chains from the later part ---------- *)
  
let rec strip_matching_ltl (a:Zparsetree.exp) (b:Zparsetree.exp)
  : Zparsetree.exp * Zparsetree.exp =
  match view_ltl a, view_ltl b with
  | Some (op1, a1), Some (op2, b1) -> if (op1 = op2 || op1 == OP_G) then
      strip_matching_ltl a1 b1 else failwith "no matching between LTL"
  | _ -> (a, b)

let strip_once a = 
  match view_ltl_zls a with 
  | Some(op1, a1) -> a1
  | None -> a

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

let is_temporal_op (s:string) = (s = "nxt" || s =  "globally" || s = "m" || s = "hd")

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
          (* Register ghost as {g:bool | g = a} *)
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

let is_operator_like_name (s:string) : bool =
  let is_op_char = function
    | '!' | '$' | '%' | '&' | '*' | '+' | '-' | '.' | '/' | ':' | '<' | '=' | '>' | '?' | '@' | '^' | '|' | '~' -> true
    | _ -> false
  in
  String.length s > 0 && String.for_all is_op_char s

let is_builtin_zpt_name (s:string) : bool =
  is_operator_like_name s ||
  List.mem s ["not"; "nxt"; "globally"; "m"; "hd"; ""]

let shift_current_vars_to_last_in_exp
    ?(shiftable_vars:string list option=None)
    ~(binder:string)
    (e:Zparsetree.exp)
  : Zparsetree.exp =
  let is_already_last s = String.length s >= 5 && String.sub s 0 5 = "last_" in
  let should_shift s =
    if s = binder || is_builtin_zpt_name s || is_already_last s then false
    else
      match shiftable_vars with
      | Some xs -> List.mem s xs
      | None -> true
  in
  let rec go e =
    match e.desc with
    | Zparsetree.Evar (Name s) ->
        if should_shift s
        then { e with desc = Zparsetree.Evar (Name ("last_" ^ s)) }
        else e
    | Zparsetree.Eapp (ai, f, args) ->
        { e with desc = Zparsetree.Eapp (ai, go f, List.map go args) }
    | Zparsetree.Etuple es ->
        { e with desc = Zparsetree.Etuple (List.map go es) }
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

(* detect equations of the form: tmp = , returning (Some (tmp, )) *)
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

(* inline all boolean witness bindings tmp = , and drop those equalities *)
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
        List.exists (fun eq -> 
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
  let g    = { loc = dummy_loc; desc = Evar (Name "globally") } in
  let x    = { loc = dummy_loc; desc = Evar (Name "nxt") } in
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
    match List.find_opt (fun vi -> vi = name) bvars with
    | None -> None
    | Some vi ->
        let i = List.find_index (fun s -> s = vi) bvars in
        match i with 
        | Some(im) ->
        if (im= j) then Some "v"                      
        else Some (List.nth t_names im)           
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

  | Zparsetree.Eapp (f, op, args) ->
      { e with desc = Zparsetree.Eapp (f, op, List.map paren_for_prec args) }

  | Zparsetree.Etuple es ->
      { e with desc = Zparsetree.Etuple (List.map paren_for_prec es) }

  | _ -> e



(* ---- Function signature table ------------------------------------------ *)
type fun_param = {
  p_name   : string;              (* source name from pattern, for debugging *)
  p_binder : string;              (* binder inside the refinement, e.g. "v"  *)
  p_base   : string;              (* base sort name, e.g. "int"              *)
  p_nf     : Zparsetree.exp;      (* normalized predicate NF for the param   *)
}

type fun_sig = {
  params     : fun_param list;    (* in declaration order                    *)
  ret_binder : string;            (* binder used in the return refinement    *)
  ret_base   : string;            (* base sort for the return                *)
  ret_nf     : Zparsetree.exp;    (* normalized predicate NF for the return  *)
}

let fun_sigs : (string, fun_sig) Hashtbl.t = Hashtbl.create 17

let zpt_base_name (ty:Zparsetree.type_expression) : string =
  match ty.desc with
  | Zparsetree.Etypeconstr (Name b, []) -> b
  | _ -> failwith "Expected base Etypeconstr(Name,[])"

(* Unpack {(v1:T1)*(v2:T2)*... | phi} into (bvars, bases, phi) *)
let tuple_refine_parts (ann_zpt : Zparsetree.type_expression)
  : (string list * string list * Zparsetree.exp) =
  match ann_zpt.desc with
  | Zparsetree.Erefinementlabeledtuple (fields, phi) ->
      let bvars =
        List.map fst fields in
      let bases =
        List.map (fun (_n, ty) ->
          match ty.desc with
          | Zparsetree.Etypeconstr (Name b, []) -> b
          | _ -> failwith "Return tuple: each base must be Etypeconstr(Name,[])"
        ) fields
      in
      (bvars, bases, phi)
  | _ -> failwith "Return tuple: expected labeled-tuple refinement"
(* --- 1) Minimal single-var renamer for Zparsetree.exp --- *)
let zpt_rename_var ~(from:string) ~(to_:string) (e:Zparsetree.exp) : Zparsetree.exp =
  let open Zparsetree in
  let rec go (e:exp) : exp =
    match e.desc with
    | Evar (Name id) ->
        if String.equal id from then { e with desc = Evar (Name to_) } else e

    | Econst _ ->
        e

    | Etuple es ->
        { e with desc = Etuple (List.map go es) }

    | Eapp (ai, f, args) ->
        let f'    = go f in
        let args' = List.map go args in
        { e with desc = Eapp (ai, f', args') }

    | Erecord fields ->
        { e with desc = Erecord (List.map (fun (lab, ei) -> (lab, go ei)) fields) }

    (* | Efield (e1, lab) ->
        { e with desc = Efield (go e1, lab) }

    | Eparen e1 ->
        { e with desc = Eparen (go e1) } *)

    (* If your AST has more cases (Eif, Elet, etc.), recurse into their children too.
       This catch-all preserves the node unchanged so the match is exhaustive. *)
    | _ -> e
  in
  go e


(* --- 2) Rename a state's LAST tuple binder to match the return binder --- *)
let rename_state_last_binder_to_return
  ~(bvars_state:string list) ~(bvars_ret:string list) (phi_state:Zparsetree.exp)
: Zparsetree.exp =
  let ks = List.length bvars_state - 1 in
  let kr = List.length bvars_ret   - 1 in
  let bs = List.nth bvars_state ks in
  let br = List.nth bvars_ret   kr in
  if String.equal bs br then phi_state
  else zpt_rename_var ~from:bs ~to_:br phi_state



let ensure_last_from_annotation
  ?(shiftable_vars:string list option=None)
  ~(source_name:string)
  ~(base_name:string)
  ~(binder:string)
  ~(ann_nf:Zparsetree.exp)
: unit =
let ghost_name = "last_" ^ source_name in
match find_binding ghost_name with
| Some _ -> ()
| None ->
    let psi = step_pred_of_ann_nf ann_nf in
    let psi = shift_current_vars_to_last_in_exp ~shiftable_vars ~binder psi in
    let psi = rename_var_in_exp binder "v" psi in
    let base_ty =
      mk_type
        (Zparsetree.Etypeconstr
            (Name (String.lowercase_ascii base_name), []))
    in
    let ghost_ty =
      { desc = Zparsetree.Erefinement (("v", base_ty), psi)
      ; loc  = dummy_loc
      }
    in
    add_binding ghost_name ghost_ty


let rec collect_plain_vars (e:Zelus.exp) : string list =
  let union a b = List.sort_uniq String.compare (a @ b) in
  match e.e_desc with
  | Zelus.Elocal { source = n; _ } -> [n]
  | Zelus.Eglobal { lname = Name n } -> [n]
  | Zelus.Etuple es
  | Zelus.Eop (_, es) ->
      List.fold_left (fun acc e -> union acc (collect_plain_vars e)) [] es
  | Zelus.Eapp (_, _f, args) ->
      List.fold_left (fun acc e -> union acc (collect_plain_vars e)) [] args
  | _ -> []

let state_name_of_pat (sp : Zelus.statepat) : string =
  match sp.desc with
  | Estate0pat id ->  zident_pretty id
  | Estate1pat (id, _args) -> zident_pretty id

let state_name_of_stateexp (se : Zelus.state_exp) : string =
  match se.desc with
  | Estate0 id -> zident_pretty id
  | Estate1 (id, _args) -> zident_pretty id


let first_state_name
    (handlers : Zelus.state_handler list)
    (init_state_opt : Zelus.state_exp option)
  : string =
  match init_state_opt with
  | Some s -> state_name_of_stateexp s
  | None ->
      match handlers with
      | h :: _ -> state_name_of_pat h.s_state
      | [] -> failwith "Empty automaton"



let rec assigned_vars_in_eq (eq:Zelus.eq) : string list =
  let union a b = List.sort_uniq String.compare (a @ b) in
  match eq.eq_desc with
  | Zelus.EQeq (pat, _rhs) ->
      begin match pat.p_desc with
      | Zelus.Evarpat id -> [zident_pretty id]
      | Zelus.Etypeconstraintpat (p0, _ty) ->
          begin match p0.p_desc with
          | Zelus.Evarpat id -> [zident_pretty id]
          | Zelus.Etuplepat ps -> List.map zelus_var_name_of_pat ps
          | _ -> []
          end
      | Zelus.Etuplepat ps -> List.map zelus_var_name_of_pat ps
      | _ -> []
      end
  | Zelus.EQand eqs
  | Zelus.EQbefore eqs
  | Zelus.EQreset (eqs, _) ->
      List.fold_left (fun acc q -> union acc (assigned_vars_in_eq q)) [] eqs
  | Zelus.EQblock blk ->
      assigned_vars_in_block blk
  | _ -> []

and assigned_vars_in_block (blk:Zelus.eq list Zelus.block) : string list =
  let union a b = List.sort_uniq String.compare (a @ b) in
  List.fold_left (fun acc q -> union acc (assigned_vars_in_eq q)) [] blk.b_body

let rec rhs_for_var_in_eq (x:string) (eq:Zelus.eq) : Zelus.exp option =
  match eq.eq_desc with
  | Zelus.EQeq (pat, rhs) ->
      begin match pat.p_desc with
      | Zelus.Evarpat id when zident_pretty id = x -> Some rhs
      | Zelus.Etypeconstraintpat (p0, _ty) ->
          begin match p0.p_desc with
          | Zelus.Evarpat id when zident_pretty id = x -> Some rhs
          | _ -> None
          end
      | _ -> None
      end

  | Zelus.EQand eqs
  | Zelus.EQbefore eqs ->
      let rec first = function
        | [] -> None
        | q::tl ->
            begin match rhs_for_var_in_eq x q with
            | Some _ as hit -> hit
            | None -> first tl
            end
      in
      first eqs

  | Zelus.EQblock blk ->
      rhs_for_var_in_block x blk

  | Zelus.EQreset (eqs, _r) ->
      let rec first = function
        | [] -> None
        | q::tl ->
            begin match rhs_for_var_in_eq x q with
            | Some _ as hit -> hit
            | None -> first tl
            end
      in
      first eqs

  | _ -> None

and rhs_for_var_in_block (x:string) (blk:Zelus.eq list Zelus.block) : Zelus.exp option =
  let rec first = function
    | [] -> None
    | q::tl ->
        begin match rhs_for_var_in_eq x q with
        | Some _ as hit -> hit
        | None -> first tl
        end
  in
  first blk.b_body

type base_ind = {
  binder    : string;
  base_name : string;
  base_phi  : Zparsetree.exp;
  ind_psi   : Zparsetree.exp;
}


let vars_of_refenv_aut (re_opt : Zelus.refenv option)
  : (string * Zelus.type_expression) list =
  match re_opt with
  | None -> []
  | Some re ->
      match re.desc with
      | Zelus.Erefenv xs -> xs

let first_state_name_aut
    (states : Zelus.state_handler_ann list)
    (init_state_opt : Zelus.state_exp option)
  : string =
  match init_state_opt with
  | Some s -> state_name_of_stateexp s
  | None ->
      match states with
      | sha :: _ -> state_name_of_pat sha.sha_handler.s_state
      | [] -> failwith "Empty automaton"

let find_state_by_name_aut
    (states : Zelus.state_handler_ann list)
    (st_name : string)
  : Zelus.state_handler_ann =
  List.find
    (fun (sha : Zelus.state_handler_ann )->
      String.equal (state_name_of_pat sha.sha_handler.s_state) st_name)
    states

let cond_of_escape (esc : Zelus.escape) : Zelus.exp option =
  match esc.e_cond.desc with
  | Zelus.Econdexp guard ->
      Some guard
  | _ ->
      None

let all_mode_names_aut (states : Zelus.state_handler_ann list) : string list =
  List.sort_uniq String.compare
    (List.map (fun ( sha : Zelus.state_handler_ann) -> state_name_of_pat sha.sha_handler.s_state) states)

let eq_const_name (varname:string) (st_name:string) : Zparsetree.exp =
  mk_eq (mk_var varname) (mk_var st_name)

let domain_of_mode_var (varname:string) (modes:string list) : Zparsetree.exp =
  mk_big_or (List.map (fun m -> eq_const_name varname m) modes)

let ensure_mode_symbol (nm:string) : unit =
  if Option.is_none (find_binding nm) then
    add_binding nm
      { desc = Zparsetree.Erefinement
          ( ("v", mk_type (Zparsetree.Etypeconstr (Name "bool", [])))
          , mk_true )
      ; loc = dummy_loc
      }

let ensure_mode_var
    ~(varname:string)
    ~(modes:string list)
  : unit =
  if Option.is_none (find_binding varname) then
    let pred = domain_of_mode_var varname modes |> rename_var_in_exp varname "v" in
    add_binding varname
      { desc = Zparsetree.Erefinement
          ( ("v", mk_type (Zparsetree.Etypeconstr (Name "bool", [])))
          , pred )
      ; loc = dummy_loc
      }

let exclusive_mode_fact (varname:string) (chosen:string) (all_modes:string list)
  : Zparsetree.exp =
  let others =
    List.filter (fun m -> not (String.equal m chosen)) all_modes
  in
  mk_big_and (
    eq_const_name varname chosen
    :: List.map (fun m -> mk_paren (mk_not (eq_const_name varname m))) others
  )