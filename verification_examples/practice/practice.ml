(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
type _exec = unit

let exec  = 
   let exec_alloc _ = () in
  let exec_reset self  =
    ((()):unit) in 
  let exec_step self () =
    ((let ((xk_21:float): float) = 1. in
      xk_21):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_32 : 'f ;
    mutable major_23 : 'e ;
    mutable h_30 : 'd ;
    mutable i_28 : 'c ; mutable h_26 : 'b ; mutable result_25 : 'a }

let main (cstate_33:Ztypes.cstate) = 
  let Node { alloc = i_32_alloc; step = i_32_step ; reset = i_32_reset } = exec 
   in
  let main_alloc _ =
    ();
    { major_23 = false ;
      h_30 = 42. ;
      i_28 = (false:bool) ; h_26 = (42.:float) ; result_25 = (():unit);
      i_32 = i_32_alloc () (* discrete *)  } in
  let main_step self ((time_22:float) , ()) =
    ((self.major_23 <- cstate_33.major ;
      (let (result_38:unit) =
           let h_29 = ref (infinity:float) in
           (if self.i_28 then self.h_26 <- (+.) time_22  0.) ;
           (let (z_27:bool) = (&&) self.major_23  ((>=) time_22  self.h_26) in
            self.h_26 <- (if z_27 then (+.) self.h_26  0.1 else self.h_26) ;
            h_29 := min !h_29  self.h_26 ;
            self.h_30 <- !h_29 ;
            self.i_28 <- false ;
            (let (trigger_24:zero) = z_27 in
             (begin match trigger_24 with
                    | true ->
                        let (x_31:float) = i_32_step self.i_32 () in
                        let _ = print_int 1 in
                        self.result_25 <- print_newline ()
                    | _ -> self.result_25 <- ()  end) ; self.result_25)) in
       cstate_33.horizon <- min cstate_33.horizon  self.h_30 ; result_38)):
    unit) in 
  let main_reset self  =
    ((self.i_28 <- true ; i_32_reset self.i_32 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
