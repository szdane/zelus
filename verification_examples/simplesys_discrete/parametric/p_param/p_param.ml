(* The Zelus compiler, version 2.2-dev
  (2026-11-2-21:7) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = (/.) (( *. ) 1.2  1.)  dt

let x0 = 0.

type ('b , 'a) _exec =
  { mutable i_49 : 'b ; mutable xk1_47 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_49 = (false:bool) ; xk1_47 = (42.:float) } in
  let exec_reset self  =
    (self.i_49 <- true:unit) in 
  let exec_step self () =
    (((if self.i_49 then self.xk1_47 <- x0) ;
      (let (l_48:float) = self.xk1_47 in
       let ((xk_46:float): float) = l_48 in
       let ((errork_44:float): float) = (-.) r  xk_46 in
       let ((uk_45:float): float) = ( *. ) kp  errork_44 in
       let ((copy_68:float): float) = (+.) xk_46  (( *. ) uk_45  dt) in
       self.xk1_47 <- copy_68 ;
       self.i_49 <- false ; (xk_46 , uk_45 , errork_44))):float *
                                                          float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_51 : 'g ;
    mutable h_58 : 'f ;
    mutable i_56 : 'e ;
    mutable h_54 : 'd ;
    mutable result_53 : 'c ; mutable i_67 : 'b ; mutable xk1_65 : 'a }

let main (cstate_70:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_51 = false ;
      h_58 = 42. ;
      i_56 = (false:bool) ;
      h_54 = (42.:float) ;
      result_53 = (():unit) ; i_67 = (false:bool) ; xk1_65 = (42.:float) } in
  let main_step self ((time_50:float) , ()) =
    ((self.major_51 <- cstate_70.major ;
      (let (result_75:unit) =
           let h_57 = ref (infinity:float) in
           (if self.i_56 then self.h_54 <- (+.) time_50  0.) ;
           (let (z_55:bool) = (&&) self.major_51  ((>=) time_50  self.h_54) in
            self.h_54 <- (if z_55 then (+.) self.h_54  0.1 else self.h_54) ;
            h_57 := min !h_57  self.h_54 ;
            self.h_58 <- !h_57 ;
            self.i_56 <- false ;
            (let (trigger_52:zero) = z_55 in
             (begin match trigger_52 with
                    | true ->
                        (if self.i_67 then self.xk1_65 <- x0) ;
                        self.i_67 <- false ;
                        (let () = () in
                         let (l_66:float) = self.xk1_65 in
                         let ((xk_64:float): float) = l_66 in
                         let ((errork_62:float): float) = (-.) r  xk_64 in
                         let ((uk_63:float): float) = ( *. ) kp  errork_62 in
                         let ((copy_69:float): float) =
                             (+.) xk_64  (( *. ) uk_63  dt) in
                         self.xk1_65 <- copy_69 ;
                         (let (error_59:float) = errork_62 in
                          let (u_60:float) = uk_63 in
                          let (x_61:float) = xk_64 in
                          let _ = print_float x_61 in
                          let _ = print_string "," in
                          let _ = print_float u_60 in
                          let _ = print_string "," in
                          let _ = print_float error_59 in
                          self.result_53 <- print_newline ()))
                    | _ -> self.result_53 <- ()  end) ; self.result_53)) in
       cstate_70.horizon <- min cstate_70.horizon  self.h_58 ; result_75)):
    unit) in 
  let main_reset self  =
    ((self.i_56 <- true ; self.i_67 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
