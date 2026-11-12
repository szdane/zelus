open Zparsetree
open Utilities

let real n = { desc = Econst (Efloat n); loc = dummy_loc }
let binary op a b = mk_app (mk_var op) [a; b]
let derive mappings =
  Liquidrefinement.differentiate_predicate
    ~derivatives:(List.map (fun (name, rhs) -> Name name, rhs) mappings)

let parse expression =
  let source = Lexing.from_string ("let predicate (x) = " ^ expression) in
  match Zparser.implementation_file Zlexer.main source with
  | [{ desc = Efundecl (_, f); _ }] -> f.f_body
  | _ -> failwith "Expected one predicate function"

let expect description expected actual =
  let printed = Pprint.string_of_expr actual in
  if printed <> expected then
    failwith (Printf.sprintf "%s: expected %s, got %s" description expected printed)

let reject description expression mappings =
  match derive mappings expression with
  | _ -> failwith (description ^ ": expected an unsupported derivative error")
  | exception Liquidrefinement.Predicate_derivative_error (_, message) ->
      assert (message <> "")

let rec arithmetic env e =
  match e.desc with
  | Econst (Eint n) -> float_of_int n
  | Econst (Efloat n) -> n
  | Evar (Name n) -> List.assoc n env
  | Eapp (_, { desc = Evar (Name op); _ }, [a; b]) ->
      let a = arithmetic env a and b = arithmetic env b in
      (match op with
       | "+." -> a +. b | "-." -> a -. b | "*." -> a *. b
       | _ -> failwith ("Unexpected arithmetic: " ^ op))
  | _ -> failwith "Unexpected arithmetic expression"

let () =
  let dx = mk_var "dx" and dy = mk_var "dy" in
  let mappings = ["x", dx; "y", dy] in
  expect "upper bound" "(dx <= 0.0)"
    (derive mappings (parse "x <= 1.0"));
  expect "interval" "((0.0 <= dx) && (dx <= 0.0))"
    (derive mappings (parse "0.0 <= x && x <= 1.0"));
  expect "strict inequality" "(dx < 0.0)"
    (derive mappings (parse "x < 1.0"));
  expect "negated inequality" "(dx > 0.0)"
    (derive mappings (parse "not (x <= 1.0)"));
  expect "disjunction requires both derivative obligations"
    "((dx < 0.0) && (dy > 0.0))"
    (derive mappings (parse "x < 1.0 || y > 2.0"));
  expect "constant parameter" "(dx <= 0.0)"
    (derive ["x", dx; "limit", real 0.0] (parse "x <= limit"));
  expect "ODE substitution is simultaneous" "(y <= 0.0)"
    (derive ["x", mk_var "y"; "y", binary "-." (real 0.0) (mk_var "x")]
       (parse "x <= 1.0"));
  expect "Boolean constant" "true" (derive [] mk_true);
  expect "parenthesized predicate" "(dx <= 0.0)"
    (derive mappings (mk_paren (parse "x <= 1.0")));
  expect "negative and subtractive terms" "((0.0 - dx) <= (dy - dx))"
    (derive mappings (parse "-. x <= y -. x"));
  (* The oscillator preserves x*x + y*y: test the symbolic result at points
     on and off the unit circle, with a nonconstant vector field. *)
  let energy = parse "x *. x +. y *. y = 1.0" in
  let energy_derivative =
    derive ["x", mk_var "y"; "y", binary "-." (real 0.0) (mk_var "x")] energy in
  (match energy_derivative.desc with
   | Eapp (_, { desc = Evar (Name "="); _ }, [lhs; rhs]) ->
       List.iter (fun (x, y) ->
         let env = ["x", x; "y", y] in
         assert (abs_float (arithmetic env lhs -. arithmetic env rhs) < 1e-10))
         [0.0, 0.0; 1.0, 0.0; 0.0, 1.0; 2.5, -3.0]
   | _ -> failwith "Expected an equality derivative");
  let stdlib_product =
    mk_app { desc = Evar (Modname {qual = Initial.stdlib_module; id = "*."}); loc = dummy_loc }
      [mk_var "x"; mk_var "y"] in
  expect "qualified standard operator" "(((dx * y) + (x * dy)) = 0.0)"
    (derive mappings (binary "=" stdlib_product (real 1.0)));
  reject "unmapped variable" (parse "x <= 1.0") [];
  let located = parse "x <= 1.0" in
  (match located.desc with
   | Eapp (_, _, [x; _]) ->
       (match derive [] located with
        | _ -> failwith "Expected a missing derivative error"
        | exception Liquidrefinement.Predicate_derivative_error (loc, _) ->
            assert (loc = x.loc))
   | _ -> failwith "Expected a comparison");
  reject "division" (parse "x /. y <= 1.0") mappings;
  reject "unknown function" (parse "sin x <= 1.0") mappings;
  reject "temporal predicate" (mk_G (parse "x <= 1.0")) mappings;
  reject "disequality" (binary "<>" (mk_var "x") (real 0.0)) mappings;
  reject "negated equality" (mk_not (parse "x = 0.0")) mappings;
  let foreign_product =
    mk_app { desc = Evar (Modname {qual = "User"; id = "*."}); loc = dummy_loc }
      [mk_var "x"; mk_var "y"] in
  reject "foreign operator" (binary "=" foreign_product (real 0.0)) mappings;
  reject "last value" (binary "=" {desc = Elast "x"; loc = dummy_loc} (real 0.0)) mappings;
  print_endline "Predicate derivative tests passed."
