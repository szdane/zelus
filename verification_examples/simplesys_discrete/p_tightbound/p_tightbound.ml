(* The Zelus compiler, version 2.2-dev
  (2026-11-4-20:25) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = (/.) (( *. ) 0.2  1.)  dt

let x0 = 0.

let error0 = (-.) r  x0

let kmin = 9.

let eps0 = 0.2

let eps = ( *. ) (( ** ) ((-.) 1.  (( *. ) kp  dt))  kmin)  error0

type ('b , 'a) _exec =
  { mutable i_56 : 'b ; mutable xk1_54 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_56 = (false:bool) ; xk1_54 = (42.:float) } in
  let exec_reset self  =
    (self.i_56 <- true:unit) in 
  let exec_step self () =
    (((if self.i_56 then self.xk1_54 <- x0) ;
      (let (l_55:float) = self.xk1_54 in
       let ((xk_53:float): float) = l_55 in
       let ((errork_50:float): float) = (-.) r  xk_53 in
       let ((uk_52:float): float) = ( *. ) kp  errork_50 in
       let ((copy_76:float): float) = (+.) xk_53  (( *. ) uk_52  dt) in
       self.xk1_54 <- copy_76 ;
       self.i_56 <- false ;
       (let ((errorkmin_51:float): float) =
            ( *. ) (( ** ) ((-.) 1.  (( *. ) kp  dt))  kmin)  errork_50 in
        let ((abs_eps_49:float): float) = ( *. ) (( ** ) (-1.)  kmin)  eps in
        (xk_53 , errork_50)))):float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_58 : 'g ;
    mutable h_65 : 'f ;
    mutable i_63 : 'e ;
    mutable h_61 : 'd ;
    mutable result_60 : 'c ; mutable i_75 : 'b ; mutable xk1_73 : 'a }

let main (cstate_78:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_58 = false ;
      h_65 = 42. ;
      i_63 = (false:bool) ;
      h_61 = (42.:float) ;
      result_60 = (():unit) ; i_75 = (false:bool) ; xk1_73 = (42.:float) } in
  let main_step self ((time_57:float) , ()) =
    ((self.major_58 <- cstate_78.major ;
      (let (result_83:unit) =
           let h_64 = ref (infinity:float) in
           (if self.i_63 then self.h_61 <- (+.) time_57  0.) ;
           (let (z_62:bool) = (&&) self.major_58  ((>=) time_57  self.h_61) in
            self.h_61 <- (if z_62 then (+.) self.h_61  0.1 else self.h_61) ;
            h_64 := min !h_64  self.h_61 ;
            self.h_65 <- !h_64 ;
            self.i_63 <- false ;
            (let (trigger_59:zero) = z_62 in
             (begin match trigger_59 with
                    | true ->
                        (if self.i_75 then self.xk1_73 <- x0) ;
                        self.i_75 <- false ;
                        (let () = () in
                         let (l_74:float) = self.xk1_73 in
                         let ((xk_72:float): float) = l_74 in
                         let ((errork_69:float): float) = (-.) r  xk_72 in
                         let ((uk_71:float): float) = ( *. ) kp  errork_69 in
                         let ((copy_77:float): float) =
                             (+.) xk_72  (( *. ) uk_71  dt) in
                         self.xk1_73 <- copy_77 ;
                         (let ((errorkmin_70:float): float) =
                              ( *. ) (( ** ) ((-.) 1.  (( *. ) kp  dt))  kmin)
                                      errork_69 in
                          let ((abs_eps_68:float): float) =
                              ( *. ) (( ** ) (-1.)  kmin)  eps in
                          let (errork_66:float) = errork_69 in
                          let (xk_67:float) = xk_72 in
                          let _ = print_float xk_67 in
                          let _ = print_string "," in
                          let _ = print_float errork_66 in
                          let _ = print_string "," in
                          let _ = print_float eps in
                          let _ = print_string "," in
                          let _ = print_float kmin in
                          let _ = print_string "," in
                          let _ = print_float r in
                          self.result_60 <- print_newline ()))
                    | _ -> self.result_60 <- ()  end) ; self.result_60)) in
       cstate_78.horizon <- min cstate_78.horizon  self.h_65 ; result_83)):
    unit) in 
  let main_reset self  =
    ((self.i_63 <- true ; self.i_75 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
