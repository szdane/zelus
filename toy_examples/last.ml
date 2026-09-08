(* The Zelus compiler, version 2.2-dev
  (2026-09-8-15:30) *)
open Ztypes
type ('a) _test =
  { mutable x_25 : 'a }

let test  = 
   let test_alloc _ =
     ();{ x_25 = (42.:float) } in
  let test_reset self  =
    (self.x_25 <- 0.:unit) in 
  let test_step self () =
    ((let ((copy_38:float): float) = 0. in
      let (l_27:float) = self.x_25 in
      self.x_25 <- copy_38 ;
      (let ((y_26:float): float) = (+.) 1.  l_27 in
       y_26)):float) in
  Node { alloc = test_alloc; reset = test_reset ; step = test_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_29 : 'e ;
    mutable h_36 : 'd ;
    mutable i_34 : 'c ; mutable h_32 : 'b ; mutable result_31 : 'a }

let main (cstate_39:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_29 = false ;
      h_36 = 42. ;
      i_34 = (false:bool) ; h_32 = (42.:float) ; result_31 = (():unit) } in
  let main_step self ((time_28:float) , ()) =
    ((self.major_29 <- cstate_39.major ;
      (let (result_44:unit) =
           let h_35 = ref (infinity:float) in
           (if self.i_34 then self.h_32 <- (+.) time_28  0.) ;
           (let (z_33:bool) = (&&) self.major_29  ((>=) time_28  self.h_32) in
            self.h_32 <- (if z_33 then (+.) self.h_32  0.1 else self.h_32) ;
            h_35 := min !h_35  self.h_32 ;
            self.h_36 <- !h_35 ;
            self.i_34 <- false ;
            (let (trigger_30:zero) = z_33 in
             (begin match trigger_30 with
                    | true ->
                        let (x_37:float) = 1. in
                        self.result_31 <- print_newline ()
                    | _ -> self.result_31 <- ()  end) ; self.result_31)) in
       cstate_39.horizon <- min cstate_39.horizon  self.h_36 ; result_44)):
    unit) in  let main_reset self  =
                (self.i_34 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
