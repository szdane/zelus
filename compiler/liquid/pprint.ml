open Zparsetree

let paren_if b s = if b then "(" ^ s ^ ")" else s
let rec needs_parens_as_arg (e: exp) =
  match e.desc with
  | Eapp _ -> true
  | _      -> false
let rec string_of_longname = function
  | Name n               -> n
  | Modname { qual; id } -> qual ^ "." ^ id
  | _ -> failwith (Printf.sprintf "Not a longname")

let pretty_float x =
  let s = string_of_float x in
  if String.length s > 0 && s.[String.length s - 1] = '.'
  then s ^ "0" else s

let rec string_of_basic_type (t : type_expression) =
  match t.desc with
  | Etypeconstr (Name "int",    []) -> "Int"
  | Etypeconstr (Name "bool",   []) -> "bool"
  | Etypeconstr (Name "real",   []) -> "real"
  | Etypeconstr (Name "float",  []) -> "real"
  | Etypeconstr (Name "string", []) -> "Str"

  (* Uninterpreted function type: func(arity,[T1,...,Tn]) *)
  | Etypefun (_, _, arg, out) ->
      "func(" ^ "1" ^ ",[" ^ string_of_basic_type arg ^ "," ^string_of_basic_type out  ^ "])"

  | Etypeconstr (ln, _) -> string_of_longname ln
  | _ -> "<complex-type>"

let is_infix op =
  List.mem op ["<"; "<="; ">"; ">="; "="; "!="; "&&"; "||"; "+"; "-"; "*"; "/"; "=>"; "-."; "+."; "*."; "/."; "==>"; "<=>"]

let rec string_of_expr (e : exp) =
  match e.desc with
  | Evar ln                    -> string_of_longname ln
  | Econst (Eint n)            -> string_of_int n
  | Econst (Ebool b)           -> string_of_bool b
  | Econst (Efloat fl)         -> pretty_float fl
  | Econst (Echar c)           -> String.make 1 c
  | Econst (Estring s)         -> Printf.sprintf "\"%s\"" s

  | Eapp (_, { desc = Evar (Name "not"); _ }, [e1]) ->
      "not (" ^ string_of_expr e1 ^ ")"

  (* Infix ops (binary) *)
  | Eapp (_, { desc = Evar (Name op); _ }, [e1; e2]) when is_infix op ->
    (match op with
    | "-." | "+." | "*." | "/." -> Printf.sprintf "(%s %s %s)" (string_of_expr e1) (String.sub op 0 1) (string_of_expr e2)
    | _ ->  Printf.sprintf "(%s %s %s)" (string_of_expr e1) op (string_of_expr e2) )

  (* Generic function application: f(a,b,...) *)
  | Eapp (_, { desc = Evar (Name f); _ }, args) ->
    let args_s =
      args
      |> List.map (fun a ->
           let sa = string_of_expr a in
           paren_if (needs_parens_as_arg a) sa)
      |> String.concat " "
    in
    if args_s = "" then f else Printf.sprintf "%s %s" f args_s

  | _ -> "<complex-expr>"

let rec string_of_type (t : type_expression) =
  match t.desc with
  | Erefinement ((v, base_ty), pred) ->
      Printf.sprintf "{%s:%s | %s}" v (string_of_basic_type base_ty) (string_of_expr pred)
  | _ -> string_of_basic_type t
