(**********************************************************************
liquidrefinement.ml – prototype integration of the Zelus AST to 
                  Liquid Fixpoint translation to the compiler
---------------------------------------------------------------------
For each binding we
1. synthesise a singleton type for the rhs,
2. query LiqF to check the singleton ≤ refinement type,
3. if SAFE we extend  with `x : annotation`.

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

open Utilities



let build_fby_pred_with_ghosts ~(binder:string)
                               ~(base:string) rhs1 rhs2
  : Zparsetree.exp =
  (* create and add ghosts *)
  let g_e = gensym "hd" in
  let g_f = gensym "tl" in
  let ty_1 = add_bool_ghost g_e mk_true in
  let ty_2 = add_bool_ghost g_f mk_true in
  let e_var = mk_var g_e in
  let f_var = mk_var g_f in
  let hd_e  = t_hd "Bool" e_var in
  let xgm_f = t_X  "Bool" (t_G "Bool" (t_M "Bool" f_var)) in
  mk_and rhs2 (mk_and (mk_paren (mk_eq (mk_var g_f) (mk_paren rhs1))) xgm_f)


let fixpoint_is_safe (fq_txt : string) : bool =
  let tmp_dir = Filename.get_temp_dir_name () in
  let tmp = Filename.temp_file ~temp_dir:tmp_dir "liq_query" ".fq" in
  let oc = open_out tmp in
  output_string oc fq_txt;
  close_out oc;
  let status = Sys.command (Printf.sprintf "fixpoint %s" (Filename.quote tmp)) in
  Sys.remove tmp;
  status = 0

let rec contains_X (e:Zparsetree.exp) : bool =
  match e.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "x"); _ }, _args) -> true
  | Zparsetree.Eapp (_, _f, args) -> List.exists contains_X args
  | Zparsetree.Etuple es          -> List.exists contains_X es
  | _ -> false
  

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
      | Zelus.Efby -> failwith (Printf.sprintf "Not handling fby for now")
      | _ -> failwith (Printf.sprintf "Not handling this Eop for now")
    )
  | Zelus.Eblock(_) -> failwith (Printf.sprintf "Not handling Eblock for now")
  (* | Zelus.Elet(_,exp) -> match exp.e_desc with
      | Econst(_) -> implementation {desc = vc_gen_expression exp; loc = dummy_loc}
      | _ -> failwith (Printf.sprintf "Not handling non constant let for now") *)
  | Zelus.Elast(id) -> Zparsetree.Evar(Name ("last_"^(zident_pretty id)))
  | _ -> failwith(Printf.sprintf "Not handling this expression")

(* v = e  &&  X true  — good "head-only" NF for comparing against _now *)
let nf_eq_v_rhs_head (e:Zelus.exp) : Zparsetree.exp =
  let v_eq = mk_eq (mk_v ()) { desc = vc_gen_expression e; loc = dummy_loc } in
  mk_and v_eq (mk_X mk_true)

(* v = e  &&  X(G(M(v = e))) — "tail" NF used for fby tails *)
let nf_eq_v_rhs_fby_tail (e:Zelus.exp) : Zparsetree.exp =
  let v_eq = mk_eq (mk_v ()) { desc = vc_gen_expression e; loc = dummy_loc } in
  mk_and v_eq (mk_X (mk_G (mk_M v_eq)))

let nf_eq_v_rhs_fby_tail_guarded ~(rhs:Zelus.exp) ~(guard:Zelus.exp)
: Zparsetree.exp =
  let loc   = dummy_loc in
  let v_eq  = mk_eq (mk_v ()) { desc = vc_gen_expression rhs;   loc } in
  let g_zpt =               { desc = vc_gen_expression guard;   loc } in
  mk_X (mk_G (mk_M (mk_and v_eq g_zpt)))


let mk_eq_v_to_zls (e_zls : Zelus.exp) name : Zparsetree.exp =
    (* let v = mk_v () in *)
    let name =  mk_var name in 
    let ez = { desc = vc_gen_expression e_zls; loc = dummy_loc } in
    mk_eq name ez

let nf_eq_v_rhs (rhs_zls:Zelus.exp) name : Zparsetree.exp =
  let v_eq = mk_eq_v_to_zls rhs_zls name in
  mk_and v_eq (mk_X (mk_G v_eq))

  
  (* Convert a Zelus predicate to ZPT expr for "now" and "next" parts *)
let zls_pred_to_nf ~(binder:string) (pred_zls:Zelus.exp) : Zparsetree.exp =
    let p = { desc = vc_gen_expression pred_zls; loc = dummy_loc } in
    (* Top-only behavior for temporal heads; otherwise, append X true
       unless an X(...) already occurs somewhere inside p. *)
    match p.desc with
    | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "g"); _}, [_]) ->
        (* e.g., G(phi)  ->  phi && X(G(phi)) *)
        let inner =
          match p.desc with
          | Zparsetree.Eapp (_, _, [q]) -> q
          | _ -> mk_true
        in
        mk_and inner (mk_X p)
  
    | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "x"); _}, [_]) ->  mk_and (mk_true) p
    | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "m"); _}, [_]) ->
        (* already X(...) or M(...):  true && X(original) *)
        mk_and (mk_true) (mk_X p)
  
    | _ ->
        (* non-temporal head: only add X true if there is no X anywhere inside *)
        if contains_X p
        then p                    
        else mk_and p (mk_X (mk_true))


let zpt_pred_to_nf ~(binder:string) (pred_zpt) : Zparsetree.exp =
  (* Top-only behavior for temporal heads; otherwise, append X true
      unless an X(...) already occurs somewhere inside p. *)
  match pred_zpt.desc with
  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "g"); _}, [_]) ->
      (* e.g., G(phi)  ->  phi && X(G(phi)) *)
      let inner =
        match pred_zpt.desc with
        | Zparsetree.Eapp (_, _, [q]) -> q
        | _ -> mk_true
      in
      mk_and (mk_paren inner) (mk_X pred_zpt)

  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "x"); _}, [_]) ->  mk_and (mk_true) pred_zpt
  | Zparsetree.Eapp (_, {desc = Zparsetree.Evar (Name "m"); _}, [_]) ->
      (* already X(...) or M(...):  true && X(original) *)
      mk_and (mk_true) (mk_X pred_zpt)

  | _ ->
      (* non-temporal head: only add X true if there is no X anywhere inside *)
      if contains_X pred_zpt
      then pred_zpt                    
      else mk_and pred_zpt (mk_X (mk_true))


      
let pred_nf_of_refine ~binder (ty:Zparsetree.type_expression) : Zparsetree.exp * string =
    match ty.desc with
    | Zparsetree.Erefinement ((vb, base_ty), pred) ->
        let pred' = if vb = binder then pred else rename_var_in_exp vb binder pred in
        (zpt_pred_to_nf ~binder pred', (* base name *) begin
          match base_ty.desc with
          | Zparsetree.Etypeconstr (Name b, []) -> b
          | _ -> failwith "pred_nf_of_refine: base must be Etypeconstr(Name,[])"
        end)
    | _ -> failwith "pred_nf_of_refine: expected refinement type"
(* Helper: extract binder, base-name, and predicate from a refinement type in 
   Assumes we always store canonical NF refinements in . *)
let refine_parts_of_gamma_ty (ty : Zparsetree.type_expression)
  : (string * string * Zparsetree.exp) =
  match ty.desc with
  | Zparsetree.Erefinement ((vb, base_ty), pred) ->
      let base_name =
        match base_ty.desc with
        | Zparsetree.Etypeconstr (Name b, []) -> b
        | _ -> failwith "Gamma binding base is not Etypeconstr(Name,[])"
      in
      (vb, base_name, pred)
  | _ -> failwith "Gamma binding is not a refinement"

let split_tuple_nf ~(binders:string list) (phi_zpt: Zparsetree.exp)
   : Zparsetree.exp * Zparsetree.exp =
   let nf = zpt_pred_to_nf ~binder:(List.hd binders) phi_zpt in
   split_nf nf


 
let debug_nf (tag:string) ~(binder:string) (pred_zls:Zelus.exp) : unit =
    let nf = zls_pred_to_nf ~binder pred_zls in
    let s_now =
      (* Show {binder | <nf>} *)
      Printf.sprintf "{%s | %s}" binder (Pprint.string_of_expr nf)
    in
    debug (Printf.sprintf "[NF:%s] %s" tag s_now)
let debug_nf_synth_lhs (rhs : Zelus.exp) : unit =
      let pp_ty (p : Zparsetree.exp) : string =
        let ty =
          { desc = Zparsetree.Erefinement (("v",
                   { desc = Zparsetree.Etypeconstr (Name "Int", []); loc = dummy_loc }),
                   p);
            loc = dummy_loc }
        in
       Pprint.string_of_type ty
      in
      match rhs.e_desc with
      | Zelus.Eop (Zelus.Eifthenelse, [c; t; e]) ->
          (* THEN branch: v = t  &&  X(G(v = t)) *)
          let p_then =
            let v_eq_t = (mk_eq_v_to_zls t "v") in
            mk_and v_eq_t (mk_X (mk_G v_eq_t))
          in
          debug (Printf.sprintf "[NF:synth LHS then] %s" (pp_ty p_then));
    
          (* ELSE branch: v = e  &&  X(G(v = e)) *)
          let p_else =
            let v_eq_e = mk_eq_v_to_zls e "v" in
            mk_and v_eq_e (mk_X (mk_G v_eq_e))
          in
          debug (Printf.sprintf "[NF:synth LHS else] %s" (pp_ty p_else))
    
      | Zelus.Eop (Zelus.Efby, [e1; e2]) ->
          (* e1 fby e2  -> v = e1  &&  X(G(M(v = e2))) *)
          let v_eq_e1 = mk_eq_v_to_zls e1 "v" in
          let v_eq_e2 = mk_eq_v_to_zls e2 "v" in
          let p = mk_and v_eq_e1 (mk_X (mk_G (mk_M v_eq_e2))) in
          debug (Printf.sprintf "[NF:synth LHS fby] %s" (pp_ty p))
    
      | _ ->
          (* default: constants/any other expr -> v = rhs && X(G(v = rhs)) *)
          let v_eq = mk_eq_v_to_zls rhs "v" in
          let p    = mk_and v_eq (mk_X (mk_G v_eq)) in
          debug (Printf.sprintf "[NF:synth LHS] %s" (pp_ty p))
  
let rec to_zpt_type (t : Zelus.type_expression) : Zparsetree.type_expression =
  let loc = dummy_loc in
  match t.desc with
  | Zelus.Etypeconstr (Name n, args) ->
      mk_type (Zparsetree.Etypeconstr (Name n, List.map to_zpt_type args))

  | Zelus.Etypetuple ts ->
      mk_type (Zparsetree.Etypetuple (List.map to_zpt_type ts))

  | Zelus.Erefinement ((vname, base_ty), pred_exp) ->
      (* debug_nf "type" ~binder:vname pred_exp; *)
      let base_zpt = to_zpt_type base_ty in
      let pred_zpt = { desc = vc_gen_expression pred_exp; loc } in
      mk_type (Zparsetree.Erefinement ((vname, base_zpt), pred_zpt))

  | Zelus.Erefinementlabeledtuple (fields, pred_exp) ->
      (* let binder_for_log =
        match fields with (n,_)::_ -> n | [] -> "_tuple"
      in
      debug_nf "type-tuple" ~binder:binder_for_log pred_exp; *)
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
  let fq_query = Gen.to_fq "v" ~cid:5 ~lhs:lhs ~rhs:rhs ~env:(current_env ()) () in
  debug (Printf.sprintf "%s" fq_query);
  fixpoint_is_safe fq_query

let rhs_var_name (e:Zelus.exp) : string option =
  match e.e_desc with
  | Zelus.Elocal { source = y } -> Some y
  | Zelus.Eglobal { lname = Name y } -> Some y
  | _ -> None


let run_subtyping_pred ~cid ~(name:string) ~(binder:string) ~(base:string)
  (lhs_pred:Zparsetree.exp) (rhs_pred:Zparsetree.exp)=
    let lhs = mk_refine binder base lhs_pred in
    let rhs = mk_refine binder base rhs_pred in
    match rhs_pred.desc with
       | Zparsetree.Econst (Ebool true) -> true
       | _ -> run_fq name lhs rhs

let nf_match_and_check ~cid ~(name:string) ~(binder:string) ~(base:string)
  (lhs_pred_nf:Zparsetree.exp) (rhs_pred_nf:Zparsetree.exp)
    : bool =
    (* 1. split into  && x  *)
    let (phi_lhs, psi_lhs) = split_nf lhs_pred_nf in
    let (phi_rhs, psi_rhs) = split_nf rhs_pred_nf in

    (* 2. “now” part *)
    
    let ok_now =
    run_subtyping_pred ~cid ~name ~binder ~base phi_lhs phi_rhs
    in
    if not ok_now then (false )else
    (* 3. strip common x/g/m chain from the “later” part *)
    let psi_lhs', psi_rhs' = strip_matching_ltl psi_lhs psi_rhs in

    (* 4. only check the “later” part when residuals are LTL-free *)
    if is_true psi_rhs' then true
    else
    if is_ltl_free psi_lhs' && is_ltl_free psi_rhs' then
    run_subtyping_pred ~cid ~name ~binder ~base psi_lhs' psi_rhs'
    else
    false
let nf_eq_v_rhs_fby_tail_guarded_zpt ~(rhs:Zelus.exp) ~(guard_zpt:Zparsetree.exp)
    : Zparsetree.exp =
    let loc   = dummy_loc in
    let v_eq  = mk_eq (mk_v ()) { desc = vc_gen_expression rhs; loc } in
    mk_X (mk_G (mk_M (mk_and v_eq guard_zpt)))
let nf_check_tail_ite_guard_on_lhs
    ~(cid:int)
    ~(name:string)
    ~(binder:string)
    ~(base:string)
    ~(ann_full:Zparsetree.exp)   
    ~(cond:Zelus.exp)
    ~(t_then:Zelus.exp)
    ~(t_else:Zelus.exp)
    : bool =
  
    let loc     = dummy_loc in
    let rhs_nf  = zpt_pred_to_nf ~binder ann_full in
    (* debug (Printf.sprintf "%s" name); *)
    (* Build GUARD and !GUARD directly as ZPT *)
    let guard_zpt     = { desc = vc_gen_expression cond; loc } in
    let guard_not_zpt = mk_not guard_zpt in
  
    let lhs_then =
      nf_eq_v_rhs_fby_tail_guarded_zpt ~rhs:t_then ~guard_zpt
    in
    let lhs_else =
      nf_eq_v_rhs_fby_tail_guarded_zpt ~rhs:t_else ~guard_zpt:guard_not_zpt
    in
  
    let ok_then =
      nf_match_and_check ~cid ~name:(name ^ ":tail-then")
        ~binder ~base lhs_then rhs_nf
    in
    if not ok_then then false else
    nf_match_and_check ~cid ~name:(name ^ ":tail-else")
      ~binder ~base lhs_else rhs_nf

let process_lhs_ty e_desc base e = 
  debug_nf_synth_lhs e; 
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

  let check_ite_branch_nf
    ~(name:string)          (* name/id for logging *)
    ~(binder:string)        (* 'v' ... *)
    ~(base:string)          (* "Int", "Bool", ... *)
    ~(cond:Zelus.exp)       (* the ITE condition c *)
    ~(rhs_branch:Zelus.exp) (* t_then or t_else *)
    ~(ann_pred:Zelus.exp)   (* original annotation predicate (Zelus) *)
    ~(guard_is_then:bool)   (* true for THEN, false for ELSE *)
    : bool =
    (* 1) Synthesized NF for this branch *)
    let lhs_nf = nf_eq_v_rhs rhs_branch "v" in

    (* 2) Normalize the annotation once *)
    let ann_nf   = zls_pred_to_nf ~binder ann_pred in
    let (phi_now, _psi_later) = split_nf ann_nf in

    (* 3) Guarded HEAD implication:
          THEN:  v = rhs sub (c => phi_now)
          ELSE:  v = rhs sub (!c => phi_now)
          (These are plain Fixpoint checks over the "now" part.)
    *)
    let lhs_head =
      singleton_type_of_const { desc = vc_gen_expression rhs_branch; loc = dummy_loc } base
    in
    let base_ty =
      mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []))
    in
    let guard =
      if guard_is_then
      then { desc = vc_gen_expression cond; loc = dummy_loc }
      else mk_app (mk_var "not") [ { desc = vc_gen_expression cond; loc = dummy_loc } ]
    in
    let rhs_head =
      mk_type (Zparsetree.Erefinement
                ((binder, base_ty),
                mk_app (mk_var "=>") [ guard; phi_now ]))
    in
    (* let ok_head = run_fq name lhs_head rhs_head in *)
    let lhs_nf = zpt_pred_to_nf ~binder (mk_app (mk_var "=>") [ guard; phi_now ]) in
    let rhs_nf = zpt_pred_to_nf ~binder (mk_app (mk_var "=>") [ guard; _psi_later ]) in
    (* if not ok_head then false else *)
    (* 4) NF-aware NEXT check:
          Compare the synthesized NF of the branch with the normalized
          annotation; strip matching X/G/M prefixes, and when both residuals
          are LTL-free, check subtyping; accept if RHS residual becomes true.
    *)
    nf_match_and_check ~cid:5 ~name ~binder ~base lhs_nf rhs_nf
    
    
  let handle_constdecl_ite ~(id:string)
  ~(binder:string)
  ~(base_name:string)
  ~(ann_pred:Zelus.exp)
  (i:Zelus.exp) (t_then:Zelus.exp) (t_else:Zelus.exp)
  (ty_ann_zpt:Zparsetree.type_expression)
  : unit =
  (* 1) Print synthesized NF for THEN and ELSE branches *)
  let nf_then = nf_eq_v_rhs t_then "v" in
  let nf_else = nf_eq_v_rhs t_else "v" in
  debug (Printf.sprintf "[NF:constdecl LHS then] %s"
  (pp_nf_as_type ~binder ~base:base_name nf_then));
  debug (Printf.sprintf "[NF:constdecl LHS else] %s"
  (pp_nf_as_type ~binder ~base:base_name nf_else));

  (* 2) Normalize the declared annotation and take only the NOW-part *)
  let ann_nf   = zls_pred_to_nf ~binder ann_pred in
  let (phi_now, _psi_later) = split_nf ann_nf in

  (* 3) Build the two implication goals against phi_now ONLY *)
  let lhs_then = singleton_type_of_const { desc = vc_gen_expression t_then; loc = dummy_loc } base_name
  in
  let lhs_else = singleton_type_of_const { desc = vc_gen_expression t_else; loc = dummy_loc } base_name
  in
  let base_ty_zpt = mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
  in
  let rhs_then =
  mk_type (Zparsetree.Erefinement
  ((binder, base_ty_zpt),
  mk_app (mk_var "=>")
  [ { desc = vc_gen_expression i; loc = dummy_loc }
  ; phi_now ]))
  in
  let rhs_else =
  mk_type (Zparsetree.Erefinement
  ((binder, base_ty_zpt),
  mk_app (mk_var "=>")
  [ mk_app (mk_var "not") [ { desc = vc_gen_expression i; loc = dummy_loc } ]
  ; phi_now ]))
  in

  (* 4) Run the two checks; if both pass, install the annotated binding *)
  (* after computing base_name, binder=v, and having pred (Zelus) *)
let ok_then =
  check_ite_branch_nf
    ~name:(id ^ ":then")
    ~binder:binder ~base:base_name
    ~cond:i ~rhs_branch:t_then ~ann_pred:ann_pred ~guard_is_then:true
in
let ok_else =
  check_ite_branch_nf
    ~name:(id ^ ":else")
    ~binder:binder ~base:base_name
    ~cond:i ~rhs_branch:t_else ~ann_pred:ann_pred ~guard_is_then:false
in
if ok_then && ok_else then
  let ann_nf = zls_pred_to_nf ~binder:binder ann_pred in
  let base_ty =
    mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
  in
  let rhs_ty =
    { desc = Zparsetree.Erefinement ((binder, base_ty), ann_nf); loc = dummy_loc }
  in
  add_binding id rhs_ty
else
  failwith (Printf.sprintf "Liquid type error: const %s (ITE) violates its annotation" id)


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
  let fq_query = Gen.to_fq "v" ~cid:1 ~lhs:lhs_ty ~rhs:rhs ~env:(current_env ()) () in
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
  let fq_query = Gen.to_fq "v" ~cid:1 ~lhs:lhs_ty ~rhs:rhs ~env:(current_env ()) () in
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
  


let singleton_with ~(binder:string) (e:Zparsetree.exp) (base_name:string)
  : Zparsetree.type_expression =
  let base_ty = mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), [])) in
  let v_var   = { desc = Zparsetree.Evar (Name binder); loc = dummy_loc } in
  let eq_op   = { desc = Zparsetree.Evar (Name "=");  loc = dummy_loc } in
  let pred    = { desc = Zparsetree.Eapp ({ app_inline = false; app_statefull = false },
                                          eq_op, [v_var; e]);
                  loc = dummy_loc } in
  mk_type (Zparsetree.Erefinement ((binder, base_ty), pred))

  
let add_fby_head_nf_binding ~(binder:string) ~(base:string) (e_head:Zelus.exp) =
    (* v = e_head *)
    let v_eq_e =
      mk_eq { desc = Zparsetree.Evar (Name "v"); loc = dummy_loc }
            { desc = vc_gen_expression e_head; loc = dummy_loc }
    in
    let hd = gensym "tmp" in
    ignore (add_bool_ghost hd mk_true);         
    let hd_var   = { desc = Zparsetree.Evar (Name hd); loc = dummy_loc } in
    let hd_def   = mk_eq hd_var (mk_paren v_eq_e) in

    let pred = mk_and v_eq_e (mk_and (mk_paren hd_def)
                            (mk_X (mk_G (mk_M hd_var)))) in
    let base_ty =
      mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []))
    in
    let ty =
      { desc = Zparsetree.Erefinement ((binder, base_ty), pred); loc = dummy_loc }
    in
    add_binding binder ty;
  ty



let process_tuple_let_fby (pat : Zelus.pattern) (rhs : Zelus.exp) : unit =
    (* 1) Parse tuple binders and the labeled-tuple refinement annotation *)
    let (xs, ann_zelus) =
      match pat.p_desc with
      | Etypeconstraintpat (bp, ann) ->
          (match bp.p_desc with
           | Etuplepat ps -> (List.map zelus_var_name_of_pat ps, ann)
           | _ -> failwith "Tuple fby: expected tuple pattern")
      | _ -> failwith "Tuple fby: expected type-constrained tuple pattern"
    in
  
    (* 2) RHS must be (e1_tuple) fby (e2_tuple) *)
    let (e1_comps, e2_comps) =
      match rhs.e_desc with
      | Zelus.Eop (Zelus.Efby, [e1; e2]) ->
          let to_tuple es =
            match es.e_desc with
            | Zelus.Etuple ts -> ts
            | _ -> failwith "Tuple fby: each branch must be a tuple expression"
          in
          (to_tuple e1, to_tuple e2)
      | _ -> failwith "Tuple fby: RHS must be (tuple1) fby (tuple2)"
    in
  
    let ar1 = List.length e1_comps
    and ar2 = List.length e2_comps
    and arx = List.length xs in
    if ar1 <> ar2 || arx <> ar1 then
      failwith "Tuple fby: arity mismatch";
  
    (* 3) Convert annotation to ZPT, extract field bases and  *)
    let ann_zpt = to_zpt_type ann_zelus in
    let (bvars, bases, phi) =
      match ann_zpt.desc with
      | Zparsetree.Erefinementlabeledtuple (fields, phi) ->
          let bnames = List.map fst fields in
          let bsorts =
            List.map (fun (_n, ty) ->
              match ty.desc with
              | Zparsetree.Etypeconstr (Name b, []) -> b
              | _ -> failwith "Tuple fby: each field base must be Etypeconstr(Name,[])"
            ) fields
          in
          (bnames, bsorts, phi)
      | _ -> failwith "Tuple fby: expected labeled-tuple refinement {(v1:τ1)*... | }"
    in
  
    (* 4) **Install ghosts FIRST** for head values of ALL components:
          Each call adds vi = e1_i && (hd_i = (vi = e1_i)) && X(G(M(hd_i))) to  *)
    let _ghosts_now : Zparsetree.type_expression list =
      List.mapi (fun i ei1 ->
        let bi   = List.nth bvars i in
        let base = List.nth bases i in
        add_fby_head_nf_binding ~binder:bi ~base ei1
      ) e1_comps
    in
  
    (* 5) Build the **single** NF check on the **last component** *)
    let k       = arx - 1 in
    let bk      = List.nth bvars k in
    let base_k  = List.nth bases k in
    let e1_k    = List.nth e1_comps k in
    let e2_k    = List.nth e2_comps k in
  
    let v_k      = mk_var bk in
    let v_eq_e1  = mk_eq v_k { desc = vc_gen_expression e1_k; loc = dummy_loc } in
    let v_eq_e2  = mk_eq v_k { desc = vc_gen_expression e2_k; loc = dummy_loc } in
    let lhs_nf_k = mk_and v_eq_e1 (mk_X (mk_G (mk_M v_eq_e2))) in
  
    let ann_nf_k = zpt_pred_to_nf ~binder:bk phi in
    
    let ok_nf =
      nf_match_and_check
        ~cid:5
        ~name:(bk ^ ":tuple-fby")
        ~binder:bk ~base:base_k
        lhs_nf_k ann_nf_k
    in
    if not ok_nf then
      failwith "Liquid type error: tuple fby NF check failed (last component)";
  
    (* 6) If OK, install the normalized annotation for each bound name *)
    let ann_nf = zpt_pred_to_nf ~binder:(List.hd bvars) phi in
    for i = 0 to arx - 1 do
      let xi      = List.nth xs i in         
      let comp_bv = List.nth bvars i in       
      let base    = List.nth bases i in
      let base_ty =
        mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []))
      in
      let ty_i =
        mk_type (Zparsetree.Erefinement ((comp_bv, base_ty), ann_nf))
      in
      add_binding xi ty_i
    done
  
  
  let process_tuple_let_eq (pat : Zelus.pattern) (rhs : Zelus.exp) : unit =
    match rhs.e_desc with
    | Zelus.Eop (Zelus.Efby, [e1; e2]) ->
        (* quick check that both are tuples *)
        (match e1.e_desc, e2.e_desc with
         | Zelus.Etuple _, Zelus.Etuple _ ->
             process_tuple_let_fby pat rhs;
             (* done *)
             ()
         | _ -> failwith "FBY should include tuple pairs");
    | _ -> 

    (
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
    List.iter (fun ei -> debug_nf_synth_lhs ei) es;
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
      | _ -> failwith "Tuple let: expected labeled-tuple refinement {(vx,vy,...) | }"
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
    let lhs_k   = List.nth ghosts k in   
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

    done)


let check_against_phi ~(fname:string)
    ~(binder:string)
    ~(base:string)
    ~(phi:Zparsetree.exp)
    (e_val:Zelus.exp) : bool =
        let lhs =
        singleton_type_of_const
        { desc = vc_gen_expression e_val; loc = dummy_loc }
        base
        in
        let rhs =
        { desc = Zparsetree.Erefinement
        ((binder,
        { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []); loc = dummy_loc }),
        phi);
        loc = dummy_loc }
        in
run_fq fname lhs rhs
let install_fby_binding ~(name:string)
                        ~(binder:string)
                        ~(base:string)
                        ~(ann_pred:Zparsetree.exp)
                        rhs1 rhs2
  : unit =

  let pred = build_fby_pred_with_ghosts ~binder ~base rhs1 rhs2 in
  let rhs_ty =
    { desc = Zparsetree.Erefinement
              ((binder,
                { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []); loc = dummy_loc }),
               pred);
      loc = dummy_loc }
  in
  add_binding name rhs_ty

  let zpt_of_cond (c:Zelus.exp) : Zparsetree.exp =
    { desc = vc_gen_expression c; loc = dummy_loc }
  
  let zpt_of_not (p:Zparsetree.exp) : Zparsetree.exp =
    mk_app (mk_var "not") [p]
  
  let zpt_eq_v_rhs (rhs_zls:Zelus.exp) : Zparsetree.exp =
    mk_eq (mk_v ()) { desc = vc_gen_expression rhs_zls; loc = dummy_loc }

  let nf_guarded_eq
      ~(binder:string)
      ~(cond_zpt:Zparsetree.exp)
      ~(rhs_zls:Zelus.exp)
    : Zparsetree.exp =
    let guard_and_eq = mk_and cond_zpt (zpt_eq_v_rhs rhs_zls) in
    zpt_pred_to_nf ~binder  (mk_and (mk_paren guard_and_eq) (mk_X (mk_G (mk_paren guard_and_eq))))
  
  

  let handle_let_ite
  ~(x:string)
  ~(ret_binder:string)
  ~(base_name:string)
  ~(ann_pred:Zelus.exp)
  (i:Zelus.exp) (t_then:Zelus.exp) (t_else:Zelus.exp)
  : unit =
  (* 1) Synthesized NFs for each branch: v = <rhs> && X(G(v = <rhs>)) *)
  let nf_then = nf_eq_v_rhs t_then "v" in
  let nf_else = nf_eq_v_rhs t_else "v" in
  debug (Printf.sprintf "[NF:let LHS then] %s"
           (pp_nf_as_type ~binder:ret_binder ~base:base_name nf_then));
  debug (Printf.sprintf "[NF:let LHS else] %s"
           (pp_nf_as_type ~binder:ret_binder ~base:base_name nf_else));

  (* 2) Normalize the declared annotation once *)
  let ann_nf = zls_pred_to_nf ~binder:ret_binder ann_pred in
  let (phi_now, _psi_later) = split_nf ann_nf in

  (* 3) Implication checks for the “now” part under guards *)
  let lhs_then =
    singleton_type_of_const { desc = vc_gen_expression t_then; loc = dummy_loc } base_name
  in
  let lhs_else =
    singleton_type_of_const { desc = vc_gen_expression t_else; loc = dummy_loc } base_name
  in
  let base_ty_zpt =
    mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
  in
  let rhs_then =
    mk_type (Zparsetree.Erefinement
               ( (ret_binder, base_ty_zpt)
               , mk_app (mk_var "=>")
                        [ { desc = vc_gen_expression i; loc = dummy_loc }
                        ; phi_now ]))
  in
  let rhs_else =
    mk_type (Zparsetree.Erefinement
               ( (ret_binder, base_ty_zpt)
               , mk_app (mk_var "=>")
                        [ mk_app (mk_var "not") [ { desc = vc_gen_expression i; loc = dummy_loc } ]
                        ; phi_now ]))
  in
  (* let ok_then_now = run_fq x lhs_then rhs_then in
  let ok_else_now = run_fq x lhs_else rhs_else in
  if not (ok_then_now && ok_else_now) then
    failwith (Printf.sprintf "Liquid type error: let-bound %s (ITE-now) violates its annotation" x); *)

  let ok_then =
    check_ite_branch_nf
      ~name:(x ^ ":then")
      ~binder:ret_binder ~base:base_name
      ~cond:i ~rhs_branch:t_then ~ann_pred:ann_pred ~guard_is_then:true
  in
  let ok_else =
    check_ite_branch_nf
      ~name:(x ^ ":else")
      ~binder:ret_binder ~base:base_name
      ~cond:i ~rhs_branch:t_else ~ann_pred:ann_pred ~guard_is_then:false
  in
  if not (ok_then&& ok_else) then
    failwith (Printf.sprintf "Liquid type error: let-bound %s (ITE-next) violates its annotation" x);
  let rhs_ty_zpt =
    { desc = Zparsetree.Erefinement ((ret_binder, base_ty_zpt), ann_nf)
    ; loc  = dummy_loc }
  in
  add_binding x rhs_ty_zpt
let ite_check_via_nf
  ~(name:string)
  ~(binder:string)
  ~(base:string)
  ~(ann_pred_zls:Zelus.exp)
  ~(cond:Zelus.exp)
  ~(t_then:Zelus.exp)
  ~(t_else:Zelus.exp)
    : bool =
    (* Normalize the declared refinement once *)
    let ann_nf = zls_pred_to_nf ~binder ann_pred_zls in

    (* Build guarded branch NFs *)
    let c_zpt   = zpt_of_cond cond in
    let notc_zpt = zpt_of_not c_zpt in

    let then_nf = nf_guarded_eq ~binder ~cond_zpt:c_zpt   ~rhs_zls:t_then in
    let else_nf = nf_guarded_eq ~binder ~cond_zpt:notc_zpt ~rhs_zls:t_else in

    (* (Optional) debug pretty-prints *)
    debug (Printf.sprintf "[NF:ITE then guarded] %s"
              (pp_nf_as_type ~binder ~base then_nf));
    debug (Printf.sprintf "[NF:ITE else guarded] %s"
              (pp_nf_as_type ~binder ~base else_nf));

    (* Both branches must satisfy the annotation NF *)
    let ok_then = nf_match_and_check ~cid:5 ~name:(name^":then") ~binder ~base then_nf ann_nf in
    let ok_else = nf_match_and_check ~cid:5 ~name:(name^":else") ~binder ~base else_nf ann_nf in
    ok_then && ok_else

(* v = e1  &&  X(G(M(v = e2)))  → normalize whole thing to NF *)
let nf_fby_eq ~(binder:string) ~(e1:Zelus.exp) ~(e2:Zelus.exp) : Zparsetree.exp =
  let v_eq_e1 = zpt_eq_v_rhs e1 in
  let v_eq_e2 = zpt_eq_v_rhs e2 in
  let whole   = mk_and v_eq_e1 (mk_X (mk_G (mk_M v_eq_e2))) in
  (* Feed through the same normalizer so we consistently end up as  && X  *)
  zpt_pred_to_nf ~binder whole

let refine_to_marvelus_nf (binder:string) (pred:Zparsetree.exp) : Zparsetree.exp =
  (* first eliminate tmp/hd witnesses *)
  let cleaned = inline_witness_bools pred in
  zpt_pred_to_nf ~binder cleaned

(* Extract (binder, base, NF) from a type in , in Marvelus NF form *)
let env_refine_nf_of_type (ty:Zparsetree.type_expression)
  : (string * string * Zparsetree.exp) =
  match ty.desc with
  | Zparsetree.Erefinement ((vb, base_ty), pred) ->
      let base =
        match base_ty.desc with
        | Zparsetree.Etypeconstr (Name b, []) -> b
        | _ -> failwith "env_refine_nf_of_type: unexpected base"
      in
      let nf = refine_to_marvelus_nf vb pred in
      (vb, base, nf)
  | _ -> failwith "env_refine_nf_of_type: expected refinement"





let nf_eq_v_rhs_fby_tail (e2: Zelus.exp) : Zparsetree.exp =
  let v = mk_v () in
  let v_eq = mk_eq v { desc = vc_gen_expression e2; loc = dummy_loc } in
  (* v = e2  &&  X(G(M(v = e2))) *)
  mk_and v_eq (mk_X (mk_G (mk_M v_eq)))

let process_let_rec_fby
  ~(x:string)
  ~(ret_binder:string)
  ~(base_name:string)
  ~(ann_pred_zls:Zelus.exp)
  (e1:Zelus.exp) (e2:Zelus.exp)
  : unit
=
  (* Normalize annotated predicate once *)
  let ann_nf  = zls_pred_to_nf ~binder:ret_binder ann_pred_zls in
  let (phi_now, _psi_later) = split_nf ann_nf in
 
 (* --- Provisional install of x with full annotation NF --- *)
  let base_ty =
    mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
  in
  let rhs_ty =
    { desc = Zparsetree.Erefinement ((ret_binder, base_ty), ann_nf)
    ; loc  = dummy_loc
    }
  in
  (* --- HEAD check: e1 sub phi_now (now-part only) --- *)
  let saved_gamma   = !gamma in
  let saved_gamma1 = !gamma1 in
  (match phi_now.desc with
  | Zparsetree.Econst (Ebool true) ->
      add_binding x rhs_ty
  | _ -> (
        let ok_head =
          check_against_phi
            ~fname:(x ^ ":rec-fby-head")
            ~binder:ret_binder
            ~base:base_name
            ~phi:phi_now
            e1
        in
        if not ok_head then
          failwith (Printf.sprintf "Liquid type error: let-rec %s head violates its annotation" x);
        add_binding x rhs_ty;           ));      

  (* --- TAIL check: compare tail-only NF vs full annotation NF --- *)
  (* Build tail-only NF: v = e2  &&  X(G(M(v = e2))) *)
  let lhs_tail_nf = nf_eq_v_rhs_fby_tail e2 in
  let ok_tail =
    nf_match_and_check
      ~cid:5
      ~name:(x ^ ":rec-fby-tail")
      ~binder:ret_binder
      ~base:base_name
      lhs_tail_nf ann_nf
  in
  if not ok_tail then begin
    (* rollback provisional binding *)
    gamma   := saved_gamma;
    gamma1 := saved_gamma1;
    failwith (Printf.sprintf "Liquid type error: let-rec %s tail violates its annotation" x)
  end;
  (* success: keep the binding we already installed *)
  ()
  
let process_let_rec_tuple_fby (pat : Zelus.pattern) (rhs : Zelus.exp) : unit =
  (* 0) Unpack pattern *)
  let (xs, ann_zelus) =
    match pat.p_desc with
    | Etypeconstraintpat (bp, ann) ->
        (match bp.p_desc with
         | Etuplepat ps ->
             (List.map zelus_var_name_of_pat ps, ann)
         | _ -> failwith "let rec tuple fby: expected tuple pattern")
    | _ -> failwith "let rec tuple fby: expected type-constrained tuple pattern"
  in

  (* RHS must be tuple fby tuple *)
  let (e1_comps, e2_comps) =
    match rhs.e_desc with
    | Zelus.Eop (Zelus.Efby, [e1; e2]) ->
        let to_tuple es =
          match es.e_desc with
          | Zelus.Etuple ts -> ts
          | _ -> failwith "let rec tuple fby: each branch must be a tuple"
        in
        (to_tuple e1, to_tuple e2)
    | _ -> failwith "let rec tuple fby: RHS must be (tuple1) fby (tuple2)"
  in
  let k = List.length xs in
  if List.length e1_comps <> k || List.length e2_comps <> k then
    failwith "let rec tuple fby: arity mismatch";

  (* 1) Parse annotation *)
  let ann_zpt = to_zpt_type ann_zelus in
  let (bvars, bases, phi) =
    match ann_zpt.desc with
    | Zparsetree.Erefinementlabeledtuple (fields, phi) ->
        let bvars = List.map fst fields in
        let bases =
          List.map (fun (_n, ty) ->
            match ty.desc with
            | Zparsetree.Etypeconstr (Name b, []) -> b
            | _ -> failwith "tuple fby: base must be Etypeconstr(Name,[])"
          ) fields
        in
        (bvars, bases, phi)
    | _ -> failwith "tuple fby: expected labeled-tuple refinement {(v1:τ1)*... | }"
  in

  (* 2) Normalize annotation  *)
  let ann_nf   = zpt_pred_to_nf ~binder:(List.nth bvars (k-1)) phi in
  let (phi_now, _psi_later) = split_nf ann_nf in

  (* 3) Head ghosts vi = ti *)
  List.iteri (fun i ei1 ->
    let bi   = List.nth bvars i in
    let base = List.nth bases i in
    ignore (add_fby_head_nf_binding ~binder:bi ~base ei1)
  ) e1_comps;

  (* 4) Head check on the last component only *)
  let idx_last = k - 1 in
  let last = (List.nth e1_comps idx_last) in
  let bi = (List.nth bvars idx_last) in
  let lhs_head_nf = nf_eq_v_rhs last bi in
  let ok_head =
    nf_match_and_check
      ~cid:5
      ~name:"tuple-fby-head"
      ~binder:(List.nth bvars idx_last)
      ~base:(List.nth bases idx_last)
      lhs_head_nf ann_nf
  in
  if not ok_head then failwith "Liquid type error: tuple fby head check failed";

  (* 5) Tail placeholders t_i with _now specialization *)
  let t_names = List.map (fun xi -> "t_" ^ xi) xs in
  List.iteri (fun j _ ->
    let base_j = List.nth bases j in
    let pred_j = phi_now_for_tj ~phi_now ~bvars ~t_names ~j in
    let ty_j =
      let open Zparsetree in
      let base_ty =
        { loc = dummy_loc; desc = Etypeconstr (Name (String.lowercase_ascii base_j), []) }
      in
      { loc = dummy_loc; desc = Erefinement (("v", base_ty), pred_j) }
    in
    add_binding (List.nth t_names j) ty_j
  ) xs;

  (* 6) Tail value ghosts vv_i = u_i[x->t] *)
  let vv_names = List.map (fun xi -> "vv_" ^ xi) xs in
  List.iteri (fun i ui ->
    let base_i = List.nth bases i in
    let ui_zpt = { Zparsetree.loc = dummy_loc; desc = vc_gen_expression ui } in
    let ui_sub = subst_xs_to_ts ~rhs_zpt:ui_zpt ~xs ~t_names in
    let ui_sub_paren = paren_for_prec ui_sub in
    let ty_vv  = singleton_eq_zpt ~binder:(List.nth vv_names i) ~base:base_i ~rhs:ui_sub_paren in
    add_binding (List.nth vv_names i) ty_vv
  ) e2_comps;

  (* 7) Tail NF check on last component only *)
  
  let idx_last = k - 1 in
  let vv_k     = List.nth vv_names idx_last in
  let base_k   = List.nth bases idx_last in
  let t_k      = List.nth t_names idx_last in

  (* Build LHS: { vv_k | vv_k = t_k } *)
  let lhs_tail_ty =
    let rhs = { Zparsetree.loc = dummy_loc; desc = Zparsetree.Evar (Name t_k) } in
    singleton_left_eq_v_zpt ~left_name:vv_k ~base:base_k
  in

  (* Build RHS predicate: _now with v_i -> vv_i, and binder v -> vv_k *)
  let phi_now_vv =
    let subst_name (nm : string) : string option =
      if String.equal nm "v" then Some vv_k
      else
        match find_index_opt nm bvars with
        | Some i -> Some (List.nth vv_names i)
        | None -> None
    in
    zpt_subst_names phi_now subst_name
  in

  let rhs_tail_ty =
    let open Zparsetree in
    let base_ty =
      { loc = dummy_loc; desc = Etypeconstr (Name (String.lowercase_ascii base_k), []) }
    in
    { loc = dummy_loc; desc = Erefinement ((vv_k, base_ty), phi_now_vv) }
  in

  (* Run the subtyping check *)
  let ok_tail = run_fq ("tuple-fby-tail:" ^ vv_k) lhs_tail_ty rhs_tail_ty in
  if not ok_tail then
    failwith "Liquid type error: tuple fby tail check failed (vv_* form)";
  
  (* 8) Install real program variables x_i with the full normalized annotation *)
  List.iteri (fun i xi ->
    let base_i = List.nth bases i in
    let base_ty =
      { Zparsetree.loc = dummy_loc
      ; desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_i), [])
      }
    in
    let ty_i =
      { Zparsetree.loc = dummy_loc
      ; desc = Zparsetree.Erefinement (("v", base_ty), ann_nf)
      }
    in
    add_binding xi ty_i;
  ) xs 




let process_scalar_eq base_pat ty_ann_zelus rhs =
    debug "Processing let eq with annotation";
    debug_nf_synth_lhs rhs;
  
    (* Bound variable name *)
    let x =
      match base_pat.p_desc with
      | Evarpat id -> zident_pretty id
      | _ -> failwith "Let pattern must be a variable with a refinement annotation"
    in
  
    (* Annotation as ZPT *)
    let ty_ann_zpt = to_zpt_type ty_ann_zelus in
    let (ret_binder, base_ty, pred_zpt) =
      match ty_ann_zpt.desc with
      | Zparsetree.Erefinement ((vb, base_ty), pred) -> (vb, base_ty, pred)
      | _ -> failwith "Expected refinement type on let-bound pattern"
    in
  
    (* For logging, show NF of the declared predicate *)
    (match ty_ann_zelus.desc with
     | Zelus.Erefinement ((_v, _base_ty), pred_exp) -> debug_nf "let" ~binder:_v pred_exp
     | Zelus.Erefinementlabeledtuple _ -> ()
     | _ -> ());
  
    (* Base sort name *)
    let base_name =
      match base_ty.desc with
      | Zparsetree.Etypeconstr (Name b, []) -> b
      | _ -> failwith "Refinement base must be Etypeconstr(Name,[])"
    in
  
    (* {v | true} fast-path *)
    (match pred_zpt.desc with
     | Zparsetree.Econst (Ebool true) ->
         add_binding x ty_ann_zpt
     | _ ->
       (* Normalize the annotation predicate once, for reuse *)
       let ann_pred_zls =
         match ty_ann_zelus.desc with
         | Zelus.Erefinement ((_vb, _base), p) -> p
         | _ -> failwith "Expected refinement type on let-bound pattern"
       in
       let ann_nf = zls_pred_to_nf ~binder:ret_binder ann_pred_zls in
  
       (* --- Alias fast-path (applies to any RHS shape): if rhs is a known var, compare (rhs) sub Ann(x) in NF. *)
       let rhs_bound_ty_opt =
         match rhs.e_desc with
         | Zelus.Elocal  { source = y }      -> find_binding y
         | Zelus.Eglobal { lname = Name y }  -> find_binding y
         | _ -> None
       in
       (match rhs_bound_ty_opt with
        | Some rhs_ty ->
          let (_vb_rhs, rhs_base, rhs_nf) = refine_parts_of_gamma_ty rhs_ty in
            if String.lowercase_ascii rhs_base <> String.lowercase_ascii base_name then
              failwith "Base mismatch between RHS variable and annotation";
            let ok =
              nf_match_and_check
                ~cid:5 ~name:("alias:" ^ x) ~binder:ret_binder ~base:base_name
                rhs_nf ann_nf
            in
            if ok then (
              (* Store normalized annotation for canonical (x) *)
              let base_ty' =
                mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
              in
              let rhs_ty' =
                { desc = Zparsetree.Erefinement ((ret_binder, base_ty'), ann_nf)
                ; loc  = dummy_loc
                }
              in
              add_binding x rhs_ty'
            ) else
              failwith (Printf.sprintf "Liquid type error: alias %s does not satisfy its annotation" x)
  
        | None ->
          (* Not an alias — fall through to shape-based handling *)
          match rhs.e_desc with
          (* FBY case: use NF rule v = e1 && X(G(M(v = e2))) *)
          | Zelus.Eop (Zelus.Efby, e1 :: e2 :: []) ->
            if expr_mentions x e2 then begin
              (* Extract the Zelus predicate from the annotation *)
              let ann_pred_zls =
                match ty_ann_zelus.desc with
                | Zelus.Erefinement ((_vb, _base), p) -> p
                | _ -> failwith "Expected refinement type on let-bound pattern"
              in
              match ann_pred_zls.e_desc with
                | Zelus.Econst (Ebool true) ->
                    add_binding x ty_ann_zpt
                | _ ->
              process_let_rec_fby
                ~x
                ~ret_binder
                ~base_name
                ~ann_pred_zls
                e1 e2
            end else begin
              let lhs_nf = nf_fby_eq ~binder:ret_binder ~e1 ~e2 in
              debug (Printf.sprintf "[NF:let LHS fby] %s"
                       (pp_nf_as_type ~binder:ret_binder ~base:base_name lhs_nf));
              debug (Printf.sprintf "[NF:let RHS ann NF] %s"
                       (pp_nf_as_type ~binder:ret_binder ~base:base_name ann_nf));
              let ok =
                nf_match_and_check
                  ~cid:5 ~name:x ~binder:ret_binder ~base:base_name
                  lhs_nf ann_nf
              in
              if ok then
                let base_ty' =
                  mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
                in
                let rhs_ty' =
                  { desc = Zparsetree.Erefinement ((ret_binder, base_ty'), ann_nf)
                  ; loc  = dummy_loc
                  }
                in
                add_binding x rhs_ty'
              else
                failwith (Printf.sprintf "Liquid type error: let-bound %s (FBY) violates its annotation" x) end
  
          (* ITE case: guard-first NF checker (both branches guarded, then NF) *)
          | Zelus.Eop (Zelus.Eifthenelse, i :: t_then :: t_else :: []) ->
              let ok =
                ite_check_via_nf
                  ~name:x ~binder:ret_binder ~base:base_name
                  ~ann_pred_zls ~cond:i ~t_then ~t_else
              in
              if ok then
                let base_ty' =
                  mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
                in
                let rhs_ty' =
                  { desc = Zparsetree.Erefinement ((ret_binder, base_ty'), ann_nf)
                  ; loc  = dummy_loc
                  }
                in
                add_binding x rhs_ty'
              else
                failwith (Printf.sprintf "Liquid type error: let-bound %s (ITE) violates its annotation" x)
  
          (* Default: synthesize v=rhs && X(G(v=rhs)) and match against ann NF *)
          | _ ->
            let ann_pred_zls =
              match ty_ann_zelus.desc with
              | Zelus.Erefinement ((_vb, _base), p) -> p
              | _ -> failwith "Expected refinement type on let-bound pattern"
            in
            let ann_nf = zls_pred_to_nf ~binder:ret_binder ann_pred_zls in
          
            (match rhs_var_name rhs with
             | Some y -> (
                 match find_binding y with
                 | Some rhs_ty ->
                     (* let (_vb_rhs, rhs_base, rhs_nf) = env_refine_nf_of_type rhs_ty in *)
                     let (_vb_rhs, rhs_base, rhs_nf) = refine_parts_of_gamma_ty rhs_ty in
                     (* if String.lowercase_ascii rhs_base <> String.lowercase_ascii base_name then
                       failwith "Base mismatch between RHS variable and annotation"; *)
                     let ok =
                       nf_match_and_check
                         ~cid:5 ~name:("alias:" ^ x) ~binder:ret_binder ~base:base_name
                         rhs_nf ann_nf
                     in
                     if ok then
                       (* Store normalized annotation for x *)
                       let base_ty =
                         mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
                       in
                       let rhs_ty_zpt =
                         { desc = Zparsetree.Erefinement ((ret_binder, base_ty), ann_nf)
                         ; loc  = dummy_loc }
                       in
                       add_binding x rhs_ty_zpt
                     else
                       failwith (Printf.sprintf "Liquid type error: alias %s does not satisfy its annotation" x)
                 | None ->
                     (* Not found in  -> fall back to synthesizing v=rhs && X(G(v=rhs)) *)
                     let v_eq_rhs = mk_eq (mk_v ()) { desc = vc_gen_expression rhs; loc = dummy_loc } in
                     let lhs_nf   = mk_and v_eq_rhs (mk_X (mk_G v_eq_rhs)) in
                     let ok_nf =
                       nf_match_and_check
                         ~cid:5 ~name:x ~binder:ret_binder ~base:base_name
                         lhs_nf ann_nf
                     in
                     let rhs_ty_zpt =
                      { desc = Zparsetree.Erefinement ((ret_binder, base_ty), ann_nf)
                      ; loc  = dummy_loc }
                     in
                     if ok_nf then add_binding x rhs_ty_zpt
                     else failwith (Printf.sprintf "Liquid type error: let-bound %s does not satisfy its annotation" x)
               )
             | None ->
                 (* RHS is not a plain variable -> original synthesized NF check *)
                 let v_eq_rhs = mk_eq (mk_v ()) { desc = vc_gen_expression rhs; loc = dummy_loc } in
                 let lhs_nf   = mk_and v_eq_rhs (mk_X (mk_G v_eq_rhs)) in
                 let ok_nf =
                   nf_match_and_check
                     ~cid:5 ~name:x ~binder:ret_binder ~base:base_name
                     lhs_nf ann_nf
                 in
                 let rhs_ty_zpt =
                  { desc = Zparsetree.Erefinement ((ret_binder, base_ty), ann_nf)
                  ; loc  = dummy_loc }
                 in
                 if ok_nf then add_binding x rhs_ty_zpt
                 else failwith (Printf.sprintf "Liquid type error: let-bound %s does not satisfy its annotation" x)
            )
       )
    )
  
    
let init_table : (string, Zelus.exp) Hashtbl.t = Hashtbl.create 16

let nf_last_of_x ~(binder:string) ~(x_name:string) ~(e_init:Zelus.exp) : Zparsetree.exp =
  let v_eq_init = mk_eq (mk_v ()) { desc = vc_gen_expression e_init; loc = dummy_loc } in
  let v_eq_x    = mk_eq (mk_v ()) (mk_var x_name) in
  zpt_pred_to_nf ~binder (mk_and v_eq_init (mk_X (mk_G (v_eq_init))))

(* Find the declared refinement for a variable in a refinement environment *)
let find_decl_in_ref_env (name:string)
                         (ref_env:(string * Zelus.type_expression) list)
  : Zelus.type_expression option =
  let rec go = function
    | [] -> None
    | (n, ty)::tl -> if String.equal n name then Some ty else go tl
  in go ref_env

(* Extract (binder, base, predicate(Zelus)) from a Zelus refinement type *)
let parts_of_zls_refine (t:Zelus.type_expression) : (string * string * Zelus.exp) =
  match t.desc with
  | Zelus.Erefinement ((vb, base_ty), pred) ->
      let base =
        match base_ty.desc with
        | Zelus.Etypeconstr (Name b, []) -> b
        | _ -> failwith "expected Etypeconstr(Name,[]) for base"
      in
      (vb, base, pred)
  | _ -> failwith "expected refinement type in ref environment"

  (* Check (init x) fby x  sub  (declared type of "last x" in the *initial* env).
   If SAFE, install "last x" into  with the normalized declared annotation. *)
let typecheck_last_x_against_init_env
    ~(x_name:string)
    ~(ref_env:(string * Zelus.type_expression) list)
  : unit =
  (* 1) Get init x; error if missing *)
  let len = Hashtbl.length init_table in
  let e_init =
    match Hashtbl.find_opt init_table x_name with
    | Some e -> e
    | None ->
        failwith (Printf.sprintf "Automaton: missing 'init %s = ...' for last %s" x_name x_name)
  in

  (* 2) Pull the declared refinement for "last x" *)
  let last_name = "last_" ^ x_name in
  let ty_decl =
    match find_decl_in_ref_env last_name ref_env with
    | Some ty -> ty
    | None ->
        failwith (Printf.sprintf "Automaton: initial env lacks a declaration for '%s'" last_name)
  in
  let (vb_decl, base_decl, pred_decl_zls) = parts_of_zls_refine ty_decl in

  (* 3) LHS NF for (init x) fby x *)
  let lhs_nf = nf_last_of_x ~binder:vb_decl ~x_name ~e_init in

  (* 4) RHS NF = normalized declared predicate *)
  let rhs_nf = zls_pred_to_nf ~binder:vb_decl pred_decl_zls in

  (* 5) NF-aware subtyping check *)
  let ok =
    nf_match_and_check
      ~cid:5
      ~name:(last_name ^ ":init-check")
      ~binder:vb_decl
      ~base:base_decl
      lhs_nf rhs_nf
  in
  if not ok then
    failwith (Printf.sprintf
      "Liquid type error: (%s) violates its initial refinement" last_name);

  (* 6) On success, install 'last x' into  with the normalized declared predicate *)
  let base_ty =
    mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_decl), []))
  in
  let rhs_ty =
    { desc = Zparsetree.Erefinement ((vb_decl, base_ty), rhs_nf)
    ; loc  = dummy_loc
    }
  in
  add_binding last_name rhs_ty
  

let rhs_for_var_in_block (x:string) (blk : Zelus.eq list Zelus.block) =
  let rec find_in_eqs = function
    | [] -> None
    | eq::tl ->
      (match eq.eq_desc with
       | EQeq (pat, rhs) ->
           (match pat.p_desc with
            | Etypeconstraintpat (bp, _ann) ->
                (* pattern is annotated: base must be a variable to match x *)
                (match bp.p_desc with
                 | Evarpat id when String.equal (zident_pretty id) x -> Some rhs
                 | _ -> find_in_eqs tl)
            | Evarpat id when String.equal (zident_pretty id) x -> Some rhs
            | _ -> find_in_eqs tl)
       | _ -> find_in_eqs tl)
  in
  find_in_eqs blk.b_body

(* Unwrap a state handler’s optional refenv into a list, or [] *)
let refenv_list_of_state (sha : Zelus.state_handler_ann) : (string * Zelus.type_expression) list =
  match sha.sha_refenv with
  | None -> []
  | Some { desc = Erefenv lst; _ } -> lst


(* Check each (var : refinement) in a state’s refenv against the state body. 
   For scalar vars, we expect an assignment [var = rhs] in the state’s do-block. *)
let check_state_against_env ~(state_name:string)
                            (sha : Zelus.state_handler_ann)
  : unit =
  let env = refenv_list_of_state sha in
  if env = [] then () else begin
    (* For each (x : {v:Base | phi}) in the state env, locate x’s assignment and check. *)
    List.iter
      (fun (x, ty_decl) ->
         (* Only handle scalar refinements here; tuples can be extended similarly *)
         match ty_decl.Zelus.desc with
         | Zelus.Erefinement ((vb, base_ty), pred_zls) ->
             (* Base sort name *)
             let base_name =
               match base_ty.desc with
               | Zelus.Etypeconstr (Name b, []) -> b
               | _ -> failwith "State env: base must be Etypeconstr(Name,[])"
             in
             (* Find [x = rhs] in the state body *)
             let rhs_opt = rhs_for_var_in_block x sha.sha_handler.s_body in
             (match rhs_opt with
              | None ->
                  failwith (Printf.sprintf
                    "Automaton[%s]: no assignment found for '%s' in state body"
                    state_name x)
              | Some rhs ->
                  (* Synthesize LHS NF for this state assignment:
                       lhs_nf = (vb = rhs) && X(G(vb = rhs))
                     IMPORTANT: use the *same binder* [vb] as in the annotation. *)
                  (* let rhs = to_zpt_type rhs.e_desc in *)
                  let lhs_nf = nf_eq_v_rhs rhs vb in

                  (* Normalize declared predicate to NF wrt binder vb *)
                  let ann_nf = zls_pred_to_nf ~binder:vb pred_zls in

                  let ok =
                    nf_match_and_check
                      ~cid:5
                      ~name:(Printf.sprintf "%s.%s" state_name x)
                      ~binder:vb
                      ~base:base_name
                      lhs_nf ann_nf
                  in
                  if not ok then
                    failwith (Printf.sprintf
                      "Liquid type error: state %s: assignment to '%s' violates its refinement"
                      state_name x)
                  else
                    (* Success: store normalized annotation for x while inside this state *)
                    let base_ty' =
                      mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
                    in
                    let rhs_ty' =
                      { desc = Zparsetree.Erefinement ((vb, base_ty'), ann_nf)
                      ; loc  = dummy_loc
                      }
                    in
                    add_binding x rhs_ty'
             )
         | Zelus.Erefinementlabeledtuple _ ->
             failwith "State env: labeled tuple refinements not handled yet"
         | _ ->
             failwith "State env: expected scalar refinement {v:Base | ...}"
      )
      env
  end

let e_false : Zparsetree.exp = { loc = dummy_loc; desc = Zparsetree.Econst (Ebool false) }

(* G(not guard) from a Zelus expression guard_zls *)
let g_not_of_guard (guard_zls) : Zparsetree.exp =
  match guard_zls with
  | None -> mk_true                            
  | Some g -> g

(* Build the guarded predicate for a state's declared refinement of ex:
   G(!guard) && P_state   where P_state is the state's predicate (already has G(...))
*)
let guarded_state_pred
    ~(state_pred_zls: Zelus.exp)
    ~(guard_zls: exp option)
  : Zparsetree.exp =
  let p_state = { loc = dummy_loc; desc = vc_gen_expression state_pred_zls } in
  let g_not   = g_not_of_guard guard_zls in
  mk_and g_not p_state

let state_refine_for_ex var_name (sha : Zelus.state_handler_ann) =
  match sha.sha_refenv with
  | None -> None
  | Some { desc = Zelus.Erefenv lst; _ } ->
      let rec go = function
        | [] -> None
        | (nm, ty)::tl ->
            if String.equal nm var_name then
              match ty.Zelus.desc with
              | Zelus.Erefinement ((vb, base_ty), pred) ->
                  let base =
                    match base_ty.desc with
                    | Zelus.Etypeconstr (Name b, []) -> b
                    | _ -> failwith "State env ex: base must be Name([])"
                  in
                  Some (vb, base, (strip_once pred))
              | _ -> failwith "State env ex: expected scalar refinement"
            else go tl
      in go lst
let zpt_of_cond (c:Zelus.exp) : Zparsetree.exp =
  { desc = vc_gen_expression c; loc = dummy_loc }


let cond_of_escape t =
  match t.Zelus.e_cond.desc with
  | Zelus.Econdexp(guard) -> Some(guard)
  | _ -> failwith "Not handling transitions except Econdexp"


let staying_guard_of_state (sha : Zelus.state_handler_ann) : Zparsetree.exp =
  let negs_zpt =
    sha.sha_handler.s_trans
    |> List.filter_map cond_of_escape
    |> List.map (fun g_zls -> mk_not { loc = dummy_loc; desc = vc_gen_expression g_zls })
  in
  match negs_zpt with
  | []      -> e_true
  | g :: gs -> List.fold_left mk_and g gs
let check_automaton_states_against_return
    ~(ret_var_name:string)  
    ~(ret_binder:string)        (* e.g., "v" from {ex:{v:int | ...}}  *)
    ~(ret_base:string)          (* e.g., "int"                         *)
    ~(ret_pred:Zelus.exp)       (* Zelus predicate in the returned env *)
    (states : Zelus.state_handler_ann list)
  : unit =
  (* Collect guarded predicates for states that declare ex in their refenv *)
  let guarded_preds : Zparsetree.exp list =
    states
    |> List.filter_map (fun sha ->
         match state_refine_for_ex ret_var_name sha with
         | None -> None
         | Some (_vb, _base, pred_ex_zls) ->
             let guard_opt = staying_guard_of_state sha in
             Some (guarded_state_pred ~state_pred_zls:pred_ex_zls ~guard_zls:(Some(guard_opt))))
  in
  if guarded_preds = [] then
    ()  (* nothing to check *)
  else
    (* Disjunction of all guarded state preds *)
    let disj =
      List.fold_left (fun acc p -> if acc == e_false then p else mk_or (mk_paren acc) (mk_paren p))
        e_false guarded_preds
    in
    (* LHS/RHS refinements with the same binder/base *)
    let lhs = mk_refine ret_binder ret_base disj in
    let rhs =
      mk_refine ret_binder ret_base { loc = dummy_loc; desc = vc_gen_expression ret_pred }
    in
    let lhs_nf = zpt_pred_to_nf ~binder:ret_binder (mk_G disj) in
    let rhs_nf = zls_pred_to_nf ~binder:ret_binder ret_pred in
    let ok =
      nf_match_and_check
        ~cid:5
        ~name:"automaton:states-vs-ret"
        ~binder:ret_binder
        ~base:ret_base
        lhs_nf rhs_nf
    in
    let rhs_ty_zpt =
      { desc =
          Zparsetree.Erefinement
            ( ("v", { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii ret_base), []); loc = dummy_loc })
            , lhs_nf);
        loc = dummy_loc }
    in
    if ok then add_binding ret_var_name rhs_ty_zpt;
    if not ok then
      failwith "Liquid type error: union of guarded state refinements does not satisfy the return environment"
let process_let_eq (eq : Zelus.eq) : unit =
      match eq.eq_desc with
      | EQeq (pat, rhs) -> begin
          match pat.p_desc with
          | Etypeconstraintpat (bp, ty_ann_zelus) -> begin
              match bp.p_desc with
              | Zelus.Etuplepat _ps -> begin
                  (* Tuple pattern: detect (tuple) fby (tuple) AND recursion *)
                  match rhs.e_desc with
                  | Zelus.Eop (Zelus.Efby, [e1; e2]) -> (
                      let is_tuple e =
                        match e.e_desc with Zelus.Etuple _ -> true | _ -> false
                      in
                      let mentions =
                        (* crude check: “let rec” in syntax is upstream; here we check semantic recursion *)
                        expr_mentions_any
                          (List.map zelus_var_name_of_pat _ps)
                          rhs
                      in
                      if is_tuple e1 && is_tuple e2 && mentions then
                        process_let_rec_tuple_fby pat rhs
                      else
                        process_tuple_let_eq pat rhs
                    )
                  | _ ->
                      process_tuple_let_eq pat rhs
                end
              | Zelus.Evarpat _ ->
                  (* existing scalar let path *)
                  process_scalar_eq bp ty_ann_zelus rhs
              | _ ->
                  failwith "Unsupported let pattern"
            end
          | _ -> ()
        end
      | EQinit(id,e) -> debug((zident_pretty id)); Hashtbl.add init_table ((zident_pretty id)) e
      | EQautomatonRef (is_weak, None, _states, _init_state, _ret_env) ->
        ()
      | EQautomatonRef (is_weak, Some ref, _states, _init_state, _ret_env) ->(
        let re = match ref.desc with
        | Erefenv(lst) -> lst in 
        let xs_from_env =
          List.filter_map
            (fun (n,_ty) ->
              if String.length n >= 5 && String.sub n 0 5 = "last_"
              then Some (String.sub n 5 (String.length n - 5))
              else None)
            re
        in
        match xs_from_env with
        | [] ->
            failwith "Automaton: couldn't find any 'last <x>' entry in the initial refinement env"
        | xs ->
            let xs = List.sort_uniq String.compare xs in
            let failures =
              List.filter_map
                (fun x ->
                   try
                     typecheck_last_x_against_init_env ~x_name:x ~ref_env:re;
                     None
                   with exn ->
                     Some (Printf.sprintf "last_%s: %s" x (Printexc.to_string exn)))
                xs
            in
            (match failures with
             | [] -> ()
             | errs ->
                 failwith
                   (Printf.sprintf
                      "Automaton: %d initial refinement error(s):\n%s"
                      (List.length errs)
                      (String.concat "\n" errs)));
        List.iter
      (fun sha ->
         let st_name =
           match sha.Zelus.sha_handler.s_state.desc with
           | Estate0pat id -> zident_pretty id
           | Estate1pat (id, _params) -> zident_pretty id
         in
         check_state_against_env ~state_name:st_name sha
      )
      _states;
      begin match _ret_env with
        | None -> ()
        | Some { desc = Zelus.Erefenv lst; _ } ->
            List.iter
              (fun (ret_var_name, ret_ty) ->
                match ret_ty.Zelus.desc with
                | Zelus.Erefinement ((ret_binder, base_ty), ret_pred_zls) ->
                    let ret_base =
                      match base_ty.desc with
                      | Zelus.Etypeconstr (Name b, []) -> b
                      | _ ->
                          failwith "Return env: base must be Etypeconstr(Name,[])."
                    in
                    check_automaton_states_against_return
                      ~ret_var_name
                      ~ret_binder
                      ~ret_base
                      ~ret_pred:ret_pred_zls
                      _states
                | _ ->
                    failwith "Return env: expected scalar refinement {v:Base | ...}.")
              lst
        end)
      | EQautomaton(_,_,_) -> ()
      | _ -> ()
    ;;
    
    

(* Convert a plain base type into {v:Base | true} *)
let refine_true_of_base (base_name:string) : Zparsetree.type_expression =
  mk_type (Zparsetree.Erefinement
             ( ("v",
                mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))),
               e_true))

(* Normalize a Zelus refinement type to ZPT and NF (phi && X psi) *)
let to_nf_refine (t:Zelus.type_expression) : Zparsetree.type_expression =
  match t.desc with
  | Zelus.Erefinement ((vb, base_ty), pred_zls) ->
      let base_zpt = to_zpt_type base_ty in
      let pred_nf  = zls_pred_to_nf ~binder:vb pred_zls in
      mk_type (Zparsetree.Erefinement ((vb, base_zpt), pred_nf))
  | Zelus.Etypeconstr (Name b, []) ->
      refine_true_of_base b
  | Zelus.Erefinementlabeledtuple (_fields, _pred) ->
      (* handled in tuple installer below *)
      failwith "to_nf_refine: labeled tuple seen in scalar position"
  | _ ->
      failwith "to_nf_refine: unsupported argument type"

(* Install a single scalar argument "x : T" into . T may be base or refinement. *)
let install_scalar_arg (x:string) (ann:Zelus.type_expression) : unit =
  let ty_nf = to_nf_refine ann in
  add_binding x ty_nf

let install_tuple_arg (ps:Zelus.pattern list) (ann:Zelus.type_expression) : unit =
  (* Build xi list from pattern *)
  let xs =
    List.map
      (fun p ->
         match p.p_desc with
         | Zelus.Evarpat id -> zident_pretty id
         | Zelus.Ealiaspat (p', _) -> (match p'.p_desc with
                                        | Zelus.Evarpat id -> zident_pretty id
                                        | _ -> failwith "Tuple arg: component must be a variable")
         | Zelus.Etypeconstraintpat (p', _) ->
              (match p'.p_desc with
               | Zelus.Evarpat id -> zident_pretty id
               | _ -> failwith "Tuple arg: nested constraint must end at a var")
         | _ -> failwith "Tuple arg: component must be a variable") ps
  in
  (* Extract bases and  from the annotated type *)
  let (bvars, bases, phi) =
    match (to_zpt_type ann).desc with
    | Zparsetree.Erefinementlabeledtuple (fields, phi) ->
        let bnames = List.map fst fields in
        let bsorts =
          List.map (fun (_n, ty) ->
            match ty.desc with
            | Zparsetree.Etypeconstr (Name b, []) -> b
            | _ -> failwith "Tuple arg: each base must be Name([])") fields
        in
        (bnames, bsorts, phi)
    | _ -> failwith "Tuple arg: expected labeled-tuple refinement {(v1:T1)*(v2:T2)*... | }"
  in
  if List.length ps <> List.length bases then
    failwith "Tuple arg: arity mismatch";

  (* Bind each xi : {vi:Base_i | } into  *)
  List.iter2
    (fun xi base_i ->
       let ty_i =
         mk_type (Zparsetree.Erefinement
                    ((xi,
                      mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_i), []))),
                     phi))
       in
       add_binding xi ty_i)
    xs bases


  
let add_annotated_arg_to_env (p : Zelus.pattern) : unit =
  match p.p_desc with
  | Zelus.Etypeconstraintpat (bp, ann_ty) ->
      (* extract the binder name from the (possibly wrapped) base pattern *)
      let x = zelus_var_name_of_pat bp in
      (* convert annotation to ZPT and normalize predicate to our NF *)
      let ann_zpt = to_zpt_type ann_ty in
      let ann_zpt_nf =
        match ann_ty.desc, ann_zpt.desc with
        | Zelus.Erefinement ((_vb_z, _base_z), pred_z), Zparsetree.Erefinement ((vb, base_zpt), _pred_zpt) ->
            let pred_nf = zls_pred_to_nf ~binder:vb pred_z in
            mk_type (Zparsetree.Erefinement ((vb, base_zpt), pred_nf))
        | _ ->
            (* not a refinement (e.g., plain base type); install as-is *)
            ann_zpt
      in
      add_binding x ann_zpt_nf
  | _ ->
      ()


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
    
    debug_nf_synth_lhs e;
    match e.e_desc with 
    | Zelus.Eop (Zelus.Eifthenelse, i :: t :: el :: []) ->
      let lhs_then =
        singleton_type_of_const { desc = vc_gen_expression t;  loc = dummy_loc } ret_base
      in
      let lhs_else =
        singleton_type_of_const { desc = vc_gen_expression el; loc = dummy_loc } ret_base
      in
      let phi =
        { desc = vc_gen_expression ret_pred; loc = dummy_loc }
      in
      let base_ty =
        mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii ret_base), []))
      in
      let rhs_then =
        mk_type (Zparsetree.Erefinement
                   ((ret_binder, base_ty),
                    mk_app (mk_var "=>")
                      [ { desc = vc_gen_expression i; loc = dummy_loc }
                      ; phi ]))
      in
      let rhs_else =
        mk_type (Zparsetree.Erefinement
                   ((ret_binder, base_ty),
                    mk_app (mk_var "=>")
                      [ mk_app (mk_var "not") [ { desc = vc_gen_expression i; loc = dummy_loc } ]
                      ; phi ]))
      in
      let ok_then = run_fq fname lhs_then rhs_then in
      let ok_else = run_fq fname lhs_else rhs_else in
      if ok_then && ok_else then ()
      else failwith (Printf.sprintf "Liquid type error: %s (return ITE) does not satisfy its annotation" fname)
      
      | Zelus.Eop (Zelus.Efby, e1 :: e2 :: []) ->
        (* Build LHS NF: v = e1  &&  X(G(M(v = e2))) *)
        let v_eq_e1 =
          mk_eq (mk_v ()) { desc = vc_gen_expression e1; loc = dummy_loc }
        in
        let v_eq_e2 =
          mk_eq (mk_v ()) { desc = vc_gen_expression e2; loc = dummy_loc }
        in
        let lhs_nf = mk_and v_eq_e1 (mk_X (mk_G (mk_M v_eq_e2))) in
  
        (* Normalize the annotated return predicate once *)
        let rhs_pred_nf = zls_pred_to_nf ~binder:ret_binder ret_pred in
  
        (* NF-aware check: compares heads, then strips x/g/m on the “later” side *)
        let ok_nf =
          nf_match_and_check
            ~cid:5 ~name:fname ~binder:ret_binder ~base:ret_base
            lhs_nf rhs_pred_nf
        in
        if ok_nf then ()
        else
          failwith (Printf.sprintf
            "Liquid type error: %s (return fby) does not satisfy its annotation" fname)
  
      | _ ->(
        (* Normalize the declared return annotation once to NF:  && X  *)
        let ann_nf = zls_pred_to_nf ~binder:ret_binder ret_pred in

        (* ALIAS FAST-PATH: if the returned expression is a variable already in _nf,
          compare its NF directly to ann_nf; do NOT synthesize v=e && X(G(v=e)). *)
        begin match rhs_var_name e with
        | Some y -> (
          match find_binding y with
          | Some rhs_ty ->
              (* let (_vb_rhs, rhs_base, rhs_nf) = env_refine_nf_of_type rhs_ty in *)
              let (_vb_rhs, rhs_base, rhs_nf) = refine_parts_of_gamma_ty rhs_ty in
                if String.lowercase_ascii rhs_base
                  <> String.lowercase_ascii ret_base
                then failwith "Return base mismatch between body variable and annotation";
                let ok =
                  nf_match_and_check
                    ~cid:5 ~name:(fname ^ ":ret-alias")
                    ~binder:ret_binder ~base:ret_base
                    rhs_nf ann_nf
                in
                if ok then ()
                else
                  failwith (Printf.sprintf
                    "Liquid type error: %s return alias does not satisfy its annotation" fname)
            | None ->
                (* Variable not found in _nf; fall back to synthesizing *)
                let v_eq = mk_eq (mk_v ()) { desc = vc_gen_expression e; loc = dummy_loc } in
                let lhs_nf = mk_and v_eq (mk_X (mk_G v_eq)) in
                let ok_nf =
                  nf_match_and_check
                    ~cid:5 ~name:fname ~binder:ret_binder ~base:ret_base
                    lhs_nf ann_nf
                in
                if ok_nf then () else
                  failwith (Printf.sprintf
                    "Liquid type error: %s does not satisfy its return annotation" fname)
          )
        | None ->
            let v_eq = mk_eq (mk_v ()) { desc = vc_gen_expression e; loc = dummy_loc } in
            let lhs_nf = mk_and v_eq (mk_X (mk_G v_eq)) in
            let ok_nf =
              nf_match_and_check
                ~cid:5 ~name:fname ~binder:ret_binder ~base:ret_base
                lhs_nf ann_nf
            in
            if ok_nf then () else
              failwith (Printf.sprintf
                "Liquid type error: %s does not satisfy its return annotation" fname)
        end)

      
  let rec check_fun_body ~(fname:string)
                         ~(ret_binder:string)
                         ~(ret_base:string)
                         ~(ret_pred:Zelus.exp)
                         (e:Zelus.exp) : unit =
    match e.e_desc with
    | Zelus.Elet (l_block, r_exp) ->
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
    | Zelus.Eop (Zelus.Eifthenelse, i :: t_then :: t_else :: []) ->
      (* rhs_ty is known to be a refinement here *)
      begin match rhs_ty.Zelus.desc with
      | Zelus.Erefinement ((v, base_ty), ann_pred) ->
          begin match base_ty.desc with
          | Zelus.Etypeconstr (Name base_name, []) ->
              (* Guard-first NF ITE check *)
              let ok = ite_check_via_nf
                          ~name:id
                          ~binder:v
                          ~base:base_name
                          ~ann_pred_zls:ann_pred
                          ~cond:i ~t_then ~t_else in
              if ok then
                (* Install normalized annotation in env *)
                let ann_nf = zls_pred_to_nf ~binder:v ann_pred in
                let base_ty_zpt =
                  mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii base_name), []))
                in
                let rhs_ty_zpt =
                  { desc = Zparsetree.Erefinement ((v, base_ty_zpt), ann_nf); loc = dummy_loc }
                in
                add_binding id rhs_ty_zpt
              else
                failwith (Printf.sprintf "Liquid type error: const %s (ITE) violates its annotation" id)
          | _ -> failwith "Not a Etypeconstr"
          end
      | _ -> failwith "Not a refinement"
        end
      | _ -> 
        (debug (Printf.sprintf "id %s" id);
        match rhs_ty.desc with
        | Zelus.Erefinement((v, base_ty), pred) ->
          debug_nf "constdecl" ~binder:v pred;
          let base =
            match base_ty.desc with
            | Zelus.Etypeconstr (Name b, []) -> b
            | _ -> failwith "Not a Etypeconstr"
          in
          let rhs_pred_nf : Zparsetree.exp = zls_pred_to_nf ~binder:v pred in
          let v_eq = mk_eq (mk_v ()) { desc = vc_gen_expression e; loc = dummy_loc } in
          let lhs_nf = mk_and v_eq (mk_X (mk_G v_eq))
          in
          let ok_nf =
            nf_match_and_check
              ~cid:5 ~name:id ~binder:"v" ~base:base
              lhs_nf rhs_pred_nf
          in
          if ok_nf then (
            let rhs_ty_zpt =
              { desc =
                  Zparsetree.Erefinement
                    ( ("v", { desc = Zparsetree.Etypeconstr (Name (String.lowercase_ascii base), []); loc = dummy_loc })
                    , rhs_pred_nf);
                loc = dummy_loc }
            in
            add_binding id rhs_ty_zpt
          ) else (
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
                    | _ -> failwith (Printf.sprintf "Not handling this Eop for now inside implementation")
                )
                (*Liquid fixpoint doesn't allow having {v:Int| c or var} only {v:base| true or false} that's why I commented out the following predicate matchings*)
                (* | Zelus.Elocal{num = i; source = n} -> failwith (Printf.sprintf "Yes it is an Elocal")
                | Zelus.Eglobal{lname = Modname qualid} -> failwith (Printf.sprintf "Yes it is an Eglobal modname") *)
                (* | Zelus.Eglobal{lname = Name var} -> process_global id v base var e *)
                | Zelus.Eglobal(_)-> process_bool id v base pred.e_desc e
                | Zelus.Econst(Ebool(_)) -> process_bool id v base pred.e_desc e
                | _ -> failwith (Printf.sprintf "Not an Eapp")
            | _ -> failwith (Printf.sprintf "Not an Etypeconstr")))
        | Etypetuple(_) -> failwith (Printf.sprintf "Not handling Etypetuple for now")
        | Erefinementlabeledtuple((x::xs, pred)) -> failwith (Printf.sprintf "Not handling Erefinementlabeledtuple for now")
        | _ ->
            failwith (Printf.sprintf "Not a refinement type")
        ))
        | Efundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
                f_body = f_body; f_loc = loc; f_retrefine = rettype }) ->
            debug (Printf.sprintf "Efundecl %s\n" n);
            debug (Printf.sprintf "# of Arguments: %d\n" (List.length p_list));

            if n = "main" then (
              debug "skipping main function";
            ) else (
              (* Parse declared return refinement exactly like before *)
              let (ret_pred_exp, ret_binder, ret_base_ty) =
                match rettype.desc with
                | Zelus.Erefinement ((vret, tbase), pred) ->
                    debug_nf "ret" ~binder:vret pred;
                    (pred, vret, tbase)
                | Zelus.Erefinementlabeledtuple (t_list, e) ->
                    (List.iter (fun (nm, _ty) -> debug_nf "ret-tuple" ~binder:nm e) t_list;
                    (e, (fst (List.hd t_list)), (snd (List.hd t_list))))
                | _ -> failwith "Not a refinement type in the return type"
              in

              let ret_base =
                match ret_base_ty.desc with
                | Zelus.Etypeconstr (Name b, []) -> b
                | _ -> failwith "Return base is not an Etypeconstr(Name,[])"
              in

              List.iter add_annotated_arg_to_env p_list;

              (* Check the function body against the declared return refinement *)
              check_fun_body n ret_binder ret_base ret_pred_exp f_body;

              let base_ty =
                mk_type (Zparsetree.Etypeconstr (Name (String.lowercase_ascii ret_base), []))
              in
              let ret_pred_nf = zls_pred_to_nf ~binder:ret_binder ret_pred_exp in
              let fun_as_value_ty =
                mk_type (Zparsetree.Erefinement (("v", base_ty), ret_pred_nf))
              in
              add_binding n fun_as_value_ty
            )


  | _ ->
      failwith (Printf.sprintf "Not a Econstdcl")


let implementation_list ff (impl_list: Zelus.implementation_desc Zelus.localized list) : Zelus.implementation_desc Zelus.localized list  =
  List.iter implementation impl_list;
  impl_list