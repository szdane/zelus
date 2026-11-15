(* The Zelus compiler, version 2.2-dev
  (2026-11-3-21:30) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

let x0 = 0.

let error0 = (-.) r  x0

let kmin = 10.

type ('b , 'a) _exec =
  { mutable i_41 : 'b ; mutable xk1_39 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_41 = (false:bool) ; xk1_39 = (42.:float) } in
  let exec_reset self  =
    (self.i_41 <- true:unit) in 
  let exec_step self () =
    (((if self.i_41 then self.xk1_39 <- x0) ;
      (let (l_40:float) = self.xk1_39 in
       let ((xk_38:float): float) = l_40 in
       let ((errork_36:float): float) = (-.) r  xk_38 in
       let ((uk_37:float): float) = ( *. ) kp  errork_36 in
       let ((copy_52:float): float) = (+.) xk_38  (( *. ) uk_37  dt) in
       self.xk1_39 <- copy_52 ;
       self.i_41 <- false ;
       (let ((errorbound_35:float): float) =
            ( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_36 in
        (xk_38 , errork_36)))):float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_43 : 'e ;
    mutable h_50 : 'd ;
    mutable i_48 : 'c ; mutable h_46 : 'b ; mutable result_45 : 'a }

let main (cstate_53:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_43 = false ;
      h_50 = 42. ;
      i_48 = (false:bool) ; h_46 = (42.:float) ; result_45 = (():unit) } in
  let main_step self ((time_42:float) , ()) =
    ((self.major_43 <- cstate_53.major ;
      (let (result_58:unit) =
           let h_49 = ref (infinity:float) in
           (if self.i_48 then self.h_46 <- (+.) time_42  0.) ;
           (let (z_47:bool) = (&&) self.major_43  ((>=) time_42  self.h_46) in
            self.h_46 <- (if z_47 then (+.) self.h_46  0.1 else self.h_46) ;
            h_49 := min !h_49  self.h_46 ;
            self.h_50 <- !h_49 ;
            self.i_48 <- false ;
            (let (trigger_44:zero) = z_47 in
             (begin match trigger_44 with
                    | true ->
                        let (x_51:float) = 1. in
                        self.result_45 <- print_newline ()
                    | _ -> self.result_45 <- ()  end) ; self.result_45)) in
       cstate_53.horizon <- min cstate_53.horizon  self.h_50 ; result_58)):
    unit) in  let main_reset self  =
                (self.i_48 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
