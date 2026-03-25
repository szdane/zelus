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

let mk_or a b =
  mk_app (mk_var "||") [a; b]

let step_pred_of_nf_later (later: Zparsetree.exp) : Zparsetree.exp =
  match later.desc with
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "globally"); _ }, [psi]) ->
      psi
  | Zparsetree.Eapp (_, { desc = Zparsetree.Evar (Name "always"); _ }, [psi]) ->
      psi
  | _ ->
      failwith
        "T-RESET expects inner synthesized type to have shape phi && X(G psi)"

let nf_reset_of_nf ~(binder:string) ~(cond:Zelus.exp) (inner_nf:Zparsetree.exp)
  : Zparsetree.exp =
  let (phi, later) = split_nf inner_nf in
  let psi = step_pred_of_nf_later later in
  let c_zpt = { desc = vc_gen_expression cond; loc = dummy_loc } in
  let step =
    mk_or
      (mk_and c_zpt phi)
      (mk_and (mk_paren(mk_not c_zpt)) psi)
  in
  mk_and phi (mk_X (mk_G step))


let ensure_last_ghost ~(x_name:string) ~(base_name:string) : unit =
  let last_name = "last_" ^ x_name in
  match find_binding last_name with
  | Some _ -> ()
  | None ->
      let base_ty =
        mk_type
          (Zparsetree.Etypeconstr
              (Name (String.lowercase_ascii base_name), []))
      in
      let ghost_ty =
        { desc = Zparsetree.Erefinement (( "v", base_ty), mk_true)
        ; loc  = dummy_loc
        }
      in
      add_binding last_name ghost_ty

      let rec collect_last_vars (e : Zelus.exp) : string list =
        let union a b =
          List.sort_uniq String.compare (a @ b)
        in
        match e.e_desc with
        | Zelus.Elast id ->
            [zident_pretty id]
      
        | Zelus.Etuple es
        | Zelus.Eop (_, es) ->
            List.fold_left (fun acc e -> union acc (collect_last_vars e)) [] es
      
        | Zelus.Eapp (_, fexp, args) ->
            List.fold_left
              (fun acc e -> union acc (collect_last_vars e))
              (collect_last_vars fexp)
              args
      
        | Zelus.Eblock (blk, eout) ->
            let rec from_eq eq =
              match eq.eq_desc with
              | Zelus.EQeq (_p, rhs) -> collect_last_vars rhs
              | Zelus.EQreset (eqs, r) ->
                  List.fold_left
                    (fun acc eq -> union acc (from_eq eq))
                    (collect_last_vars r)
                    eqs
              | _ -> []
            in
            List.fold_left
              (fun acc eq -> union acc (from_eq eq))
              (collect_last_vars eout)
              blk.b_body
        | Zelus.Eassume e1 ->
            collect_last_vars e1
      
        | Zelus.Erecord fields ->
            List.fold_left
              (fun acc (_lbl, e) -> union acc (collect_last_vars e))
              []
              fields
      
        | Zelus.Erecord_with (e0, fields) ->
            List.fold_left
              (fun acc (_lbl, e) -> union acc (collect_last_vars e))
              (collect_last_vars e0)
              fields
      
        | Zelus.Ematch (_tot, e0, _hs) ->
            collect_last_vars e0
      
        | Zelus.Epresent (_hs, eo) ->
            begin match eo with
            | None -> []
            | Some e -> collect_last_vars e
            end
      
        | _ -> []

let var_name_with_last_depth (base:string) (depth:int) : string =
  let rec aux acc d =
    if d <= 0 then acc else aux ("last_" ^ acc) (d - 1)
  in
  aux base depth

let rec collect_shifted_ghost_names ~(shift:int) (e:Zelus.exp) : string list =
  let union a b = List.sort_uniq String.compare (a @ b) in

  let from_list es =
    List.fold_left
      (fun acc e -> union acc (collect_shifted_ghost_names ~shift e))
      []
      es
  in

  let rec from_eq (eq:Zelus.eq) : string list =
    match eq.eq_desc with
    | Zelus.EQeq (_p, rhs) ->
        collect_shifted_ghost_names ~shift rhs

    | Zelus.EQreset (eqs, r) ->
        List.fold_left
          (fun acc eq -> union acc (from_eq eq))
          (collect_shifted_ghost_names ~shift r)
          eqs

    | Zelus.EQand eqs ->
        List.fold_left
          (fun acc eq -> union acc (from_eq eq))
          []
          eqs

    | _ ->
        []
  in

  match e.e_desc with
  | Zelus.Econst _ ->
      []

  | Zelus.Eglobal { lname = Name n } ->
      [var_name_with_last_depth n shift]

  | Zelus.Eglobal { lname = Modname qualid } ->
      [var_name_with_last_depth qualid.id shift]

  | Zelus.Elocal { source = n; _ } ->
      [var_name_with_last_depth n shift]

  | Zelus.Elast id ->
      [var_name_with_last_depth (zident_pretty id) (shift + 1)]

  | Zelus.Etuple es ->
      from_list es

  | Zelus.Eop (_, es) ->
      from_list es

  | Zelus.Eapp (_, fexp, args) -> from_list args

  | Zelus.Eblock (blk, eout) ->
      List.fold_left
        (fun acc eq -> union acc (from_eq eq))
        (collect_shifted_ghost_names ~shift eout)
        blk.b_body

  | Zelus.Elet (_, e1)
  | Zelus.Etypeconstraint (e1, _)
  | Zelus.Erecord_access (e1, _)
  | Zelus.Eassume e1
  | Zelus.Erefinementtype (_, _, e1) ->
      collect_shifted_ghost_names ~shift e1

  | Zelus.Erecord fields ->
      List.fold_left
        (fun acc (_lbl, e) ->
            union acc (collect_shifted_ghost_names ~shift e))
        []
        fields

  | Zelus.Erecord_with (e0, fields) ->
      List.fold_left
        (fun acc (_lbl, e) ->
            union acc (collect_shifted_ghost_names ~shift e))
        (collect_shifted_ghost_names ~shift e0)
        fields

  | Zelus.Ematch (_tot, e0, _hs) ->
      collect_shifted_ghost_names ~shift e0

  | Zelus.Epresent (_hs, eo) ->
      begin match eo with
      | None -> []
      | Some e -> collect_shifted_ghost_names ~shift e
      end

  | _ ->
      []

let ensure_named_ghost ~(ghost_name:string) ~(base_name:string) : unit =
  match find_binding ghost_name with
  | Some _ -> ()
  | None ->
      let base_ty =
        mk_type
          (Zparsetree.Etypeconstr
              (Name (String.lowercase_ascii base_name), []))
      in
      let ghost_ty =
        { desc = Zparsetree.Erefinement (("v", base_ty), mk_true)
        ; loc  = dummy_loc
        }
      in
      add_binding ghost_name ghost_ty