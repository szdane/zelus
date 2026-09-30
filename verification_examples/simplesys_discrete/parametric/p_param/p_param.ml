(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

type ('a) _exec =
  { mutable xk1_45 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ xk1_45 = (42.:float) } in
  let exec_reset self  =
    (self.xk1_45 <- 0.:unit) in 
  let exec_step self () =
    ((let (l_46:float) = self.xk1_45 in
      let ((xk_44:float): float) = l_46 in
      let ((errork_42:float): float) = (-.) r  xk_44 in
      let ((uk_43:float): float) = ( *. ) kp  errork_42 in
      let ((copy_64:float): float) = (+.) xk_44  (( *. ) uk_43  dt) in
      self.xk1_45 <- copy_64 ; (xk_44 , uk_43 , errork_42)):float *
                                                            float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_48 : 'f ;
    mutable h_55 : 'e ;
    mutable i_53 : 'd ;
    mutable h_51 : 'c ; mutable result_50 : 'b ; mutable xk1_62 : 'a }

let main (cstate_66:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_48 = false ;
      h_55 = 42. ;
      i_53 = (false:bool) ;
      h_51 = (42.:float) ; result_50 = (():unit) ; xk1_62 = (42.:float) } in
  let main_step self ((time_47:float) , ()) =
    ((self.major_48 <- cstate_66.major ;
      (let (result_71:unit) =
           let h_54 = ref (infinity:float) in
           (if self.i_53 then self.h_51 <- (+.) time_47  0.) ;
           (let (z_52:bool) = (&&) self.major_48  ((>=) time_47  self.h_51) in
            self.h_51 <- (if z_52 then (+.) self.h_51  0.1 else self.h_51) ;
            h_54 := min !h_54  self.h_51 ;
            self.h_55 <- !h_54 ;
            self.i_53 <- false ;
            (let (trigger_49:zero) = z_52 in
             (begin match trigger_49 with
                    | true ->
                        let () = () in
                        let (l_63:float) = self.xk1_62 in
                        let ((xk_61:float): float) = l_63 in
                        let ((errork_59:float): float) = (-.) r  xk_61 in
                        let ((uk_60:float): float) = ( *. ) kp  errork_59 in
                        let ((copy_65:float): float) =
                            (+.) xk_61  (( *. ) uk_60  dt) in
                        self.xk1_62 <- copy_65 ;
                        (let (error_56:float) = errork_59 in
                         let (u_57:float) = uk_60 in
                         let (x_58:float) = xk_61 in
                         let _ = print_float x_58 in
                         let _ = print_string "," in
                         let _ = print_float u_57 in
                         let _ = print_string "," in
                         let _ = print_float error_56 in
                         self.result_50 <- print_newline ())
                    | _ -> self.result_50 <- ()  end) ; self.result_50)) in
       cstate_66.horizon <- min cstate_66.horizon  self.h_55 ; result_71)):
    unit) in 
  let main_reset self  =
    ((self.i_53 <- true ; self.xk1_62 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
