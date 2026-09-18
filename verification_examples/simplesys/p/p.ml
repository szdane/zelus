(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

type ('a) _exec =
  { mutable m_43 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ m_43 = (42.:float) } in
  let exec_reset self  =
    (self.m_43 <- 0.:unit) in 
  let exec_step self () =
    ((let (next_44:float) = self.m_43 in
      let ((xk_42:float): float) = next_44 in
      let ((errork_40:float): float) = (-.) r  xk_42 in
      let ((uk_41:float): float) = ( *. ) kp  errork_40 in
      self.m_43 <- (+.) xk_42  (( *. ) (( *. ) 2.  ((-.) 1.  xk_42))  0.1) ;
      (xk_42 , uk_41 , errork_40)):float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_46 : 'f ;
    mutable h_53 : 'e ;
    mutable i_51 : 'd ;
    mutable h_49 : 'c ; mutable result_48 : 'b ; mutable m_60 : 'a }

let main (cstate_62:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_46 = false ;
      h_53 = 42. ;
      i_51 = (false:bool) ;
      h_49 = (42.:float) ; result_48 = (():unit) ; m_60 = (42.:float) } in
  let main_step self ((time_45:float) , ()) =
    ((self.major_46 <- cstate_62.major ;
      (let (result_67:unit) =
           let h_52 = ref (infinity:float) in
           (if self.i_51 then self.h_49 <- (+.) time_45  0.) ;
           (let (z_50:bool) = (&&) self.major_46  ((>=) time_45  self.h_49) in
            self.h_49 <- (if z_50 then (+.) self.h_49  0.1 else self.h_49) ;
            h_52 := min !h_52  self.h_49 ;
            self.h_53 <- !h_52 ;
            self.i_51 <- false ;
            (let (trigger_47:zero) = z_50 in
             (begin match trigger_47 with
                    | true ->
                        let () = () in
                        let (next_61:float) = self.m_60 in
                        let ((xk_59:float): float) = next_61 in
                        self.m_60 <- (+.) xk_59 
                                          (( *. ) (( *. ) 2. 
                                                          ((-.) 1.  xk_59)) 
                                                  0.1) ;
                        (let ((errork_57:float): float) = (-.) r  xk_59 in
                         let (error_54:float) = errork_57 in
                         let ((uk_58:float): float) = ( *. ) kp  errork_57 in
                         let (u_55:float) = uk_58 in
                         let (x_56:float) = xk_59 in
                         let _ = print_float x_56 in
                         let _ = print_string "," in
                         let _ = print_float u_55 in
                         let _ = print_string "," in
                         let _ = print_float error_54 in
                         self.result_48 <- print_newline ())
                    | _ -> self.result_48 <- ()  end) ; self.result_48)) in
       cstate_62.horizon <- min cstate_62.horizon  self.h_53 ; result_67)):
    unit) in 
  let main_reset self  =
    ((self.i_51 <- true ; self.m_60 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
