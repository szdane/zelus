(* The Zelus compiler, version 2.2-dev
  (2026-09-11-18:30) *)
open Ztypes
let energy (((x_29:float): float) , ((y_30:float): float)) =
  (2. , 3.)

let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_32 : 'e ;
    mutable h_39 : 'd ;
    mutable i_37 : 'c ; mutable h_35 : 'b ; mutable result_34 : 'a }

let main (cstate_44:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_32 = false ;
      h_39 = 42. ;
      i_37 = (false:bool) ; h_35 = (42.:float) ; result_34 = (():unit) } in
  let main_step self ((time_31:float) , ()) =
    ((self.major_32 <- cstate_44.major ;
      (let (result_49:unit) =
           let h_38 = ref (infinity:float) in
           (if self.i_37 then self.h_35 <- (+.) time_31  0.) ;
           (let (z_36:bool) = (&&) self.major_32  ((>=) time_31  self.h_35) in
            self.h_35 <- (if z_36 then (+.) self.h_35  dt else self.h_35) ;
            h_38 := min !h_38  self.h_35 ;
            self.h_39 <- !h_38 ;
            self.i_37 <- false ;
            (let (trigger_33:zero) = z_36 in
             (begin match trigger_33 with
                    | true ->
                        let ((x_42:float): float) = 1. in
                        let ((y_43:float): float) = 1. in
                        let (y_41:float) = 3. in
                        let (x_40:float) = 2. in
                        let _ = print_float x_40 in
                        self.result_34 <- print_newline ()
                    | _ -> self.result_34 <- ()  end) ; self.result_34)) in
       cstate_44.horizon <- min cstate_44.horizon  self.h_39 ; result_49)):
    unit) in  let main_reset self  =
                (self.i_37 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
