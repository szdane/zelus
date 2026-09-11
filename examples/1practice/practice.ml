(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let calc (((x_33:float): float) , ((y_34:float): float)) =
  let ((z_35:float): float) = (+.) x_33  0. in
  z_35

type _test = unit

let test  = 
   let test_alloc _ = () in
  let test_reset self  =
    ((()):unit) in 
  let test_step self () =
    ((let ((y_37:float): float) = 2. in
      let ((x_36:float): float) = 1. in
      (x_36 , y_37)):float * float) in
  Node { alloc = test_alloc; reset = test_reset ; step = test_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_39 : 'e ;
    mutable h_46 : 'd ;
    mutable i_44 : 'c ; mutable h_42 : 'b ; mutable result_41 : 'a }

let main (cstate_48:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_39 = false ;
      h_46 = 42. ;
      i_44 = (false:bool) ; h_42 = (42.:float) ; result_41 = (():unit) } in
  let main_step self ((time_38:float) , ()) =
    ((self.major_39 <- cstate_48.major ;
      (let (result_53:unit) =
           let h_45 = ref (infinity:float) in
           (if self.i_44 then self.h_42 <- (+.) time_38  0.) ;
           (let (z_43:bool) = (&&) self.major_39  ((>=) time_38  self.h_42) in
            self.h_42 <- (if z_43 then (+.) self.h_42  0.1 else self.h_42) ;
            h_45 := min !h_45  self.h_42 ;
            self.h_46 <- !h_45 ;
            self.i_44 <- false ;
            (let (trigger_40:zero) = z_43 in
             (begin match trigger_40 with
                    | true ->
                        let (aaa_47:float) = 1. in
                        self.result_41 <- print_newline ()
                    | _ -> self.result_41 <- ()  end) ; self.result_41)) in
       cstate_48.horizon <- min cstate_48.horizon  self.h_46 ; result_53)):
    unit) in  let main_reset self  =
                (self.i_44 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
