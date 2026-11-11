(* The Zelus compiler, version 2.2-dev
  (2026-11-11-22:45) *)
open Ztypes
type ('a) _exec =
  { mutable xk1_32 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ xk1_32 = (42.:float) } in
  let exec_reset self  =
    (self.xk1_32 <- 0.:unit) in 
  let exec_step self () =
    ((let (l_33:float) = self.xk1_32 in
      let ((xk_31:float): float) = l_33 in
      let ((copy_48:float): float) = (+.) xk_31  1. in
      self.xk1_32 <- copy_48 ; (xk_31 , self.xk1_32)):float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_35 : 'f ;
    mutable h_42 : 'e ;
    mutable i_40 : 'd ;
    mutable h_38 : 'c ; mutable result_37 : 'b ; mutable xk1_46 : 'a }

let main (cstate_50:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_35 = false ;
      h_42 = 42. ;
      i_40 = (false:bool) ;
      h_38 = (42.:float) ; result_37 = (():unit) ; xk1_46 = (42.:float) } in
  let main_step self ((time_34:float) , ()) =
    ((self.major_35 <- cstate_50.major ;
      (let (result_55:unit) =
           let h_41 = ref (infinity:float) in
           (if self.i_40 then self.h_38 <- (+.) time_34  0.) ;
           (let (z_39:bool) = (&&) self.major_35  ((>=) time_34  self.h_38) in
            self.h_38 <- (if z_39 then (+.) self.h_38  0.1 else self.h_38) ;
            h_41 := min !h_41  self.h_38 ;
            self.h_42 <- !h_41 ;
            self.i_40 <- false ;
            (let (trigger_36:zero) = z_39 in
             (begin match trigger_36 with
                    | true ->
                        let () = () in
                        let (l_47:float) = self.xk1_46 in
                        let ((xk_45:float): float) = l_47 in
                        let ((copy_49:float): float) = (+.) xk_45  1. in
                        self.xk1_46 <- copy_49 ;
                        (let (x1_44:float) = self.xk1_46 in
                         let (x_43:float) = xk_45 in
                         let _ = print_float x_43 in
                         let _ = print_string " " in
                         let _ = print_float x1_44 in
                         self.result_37 <- print_newline ())
                    | _ -> self.result_37 <- ()  end) ; self.result_37)) in
       cstate_50.horizon <- min cstate_50.horizon  self.h_42 ; result_55)):
    unit) in 
  let main_reset self  =
    ((self.i_40 <- true ; self.xk1_46 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
