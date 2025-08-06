(*------------------------------------------------------------------
testliquid.ml  –  tiny driver that fabricates a Zelus AST with one
                    constant declaration and feeds it into
                    Liquidrefinement.implementation_list
------------------------------------------------------------------*)

open Zparsetree
open Liquidrefinement  

let loc = Zlocation.no_location

let base_int  =
  { desc  = Etypeconstr (Name "int", []); loc = loc}

let v_var   = { desc = Evar (Name "v"); loc = loc }
let zero    = { desc = Econst (Eint 0);    loc = loc }
let gt_op   = { desc = Evar (Name ">");  loc = loc }
let pred    = { desc = Eapp ({ app_inline=false; app_statefull=false },
                                gt_op, [v_var; zero]);
                  loc = loc }

let rhs_ty  =
  { desc  = Erefinement (("v", base_int), pred); loc = loc }

let five_exp = { desc = Econst (Eint 5); loc = loc }
let x_var = {desc = Evar (Name "x"); loc = loc}

let x_plus_c = {desc = Eapp ({app_inline=false; app_statefull=false}, 
                {desc = Evar (Name "+"); loc = loc}, [x_var;five_exp]); loc = loc}

let x_minus_c = {desc = Eapp ({app_inline=false; app_statefull=false}, 
{desc = Evar (Name "-"); loc = loc}, [x_var;five_exp]); loc = loc}

let x_times_c = {desc = Eapp ({app_inline=false; app_statefull=false}, 
{desc = Evar (Name "*"); loc = loc}, [x_var;five_exp]); loc = loc}

let x_div_c = {desc = Eapp ({app_inline=false; app_statefull=false}, 
{desc = Evar (Name "/"); loc = loc}, [x_var;five_exp]); loc = loc}


let const_decl1 : implementation_desc localized =
  { desc = Econstdecl ("x", rhs_ty, false, five_exp);
    loc  }
  
let const_decl2 : implementation_desc localized =
  { desc = Econstdecl ("y", rhs_ty, false, x_plus_c);
    loc  }

let () =
  let _ = implementation_list () [const_decl1; const_decl2] in
  print_endline "✓ Liquid refinement check passed for test program."
