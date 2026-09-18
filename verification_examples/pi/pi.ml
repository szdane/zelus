(* The Zelus compiler, version 2.2-dev
  (2026-08-31-21:11) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let dt = 0.1

type ('b , 'a) _exec =
  { mutable xk1_60 : 'b ; mutable integralk_56 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();{ xk1_60 = (42.:float) ; integralk_56 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_60 <- 0. ; self.integralk_56 <- 0.):unit) in 
  let exec_step self () =
    ((let (l_62:float) = self.xk1_60 in
      let ((xk_59:float): float) = l_62 in
      let ((errork_55:float): float) = (-.) r  xk_59 in
      let (l_61:float) = self.integralk_56 in
      let ((integralkm1_57:float): float) = l_61 in
      let ((uk_58:float): float) =
          (+.) (( *. ) kp  errork_55)  (( *. ) ki  integralkm1_57) in
      let ((copy_84:float): float) = (+.) xk_59  (( *. ) uk_58  dt) in
      self.xk1_60 <- copy_84 ;
      (let ((copy_85:float): float) =
           (+.) integralkm1_57  (( *. ) errork_55  dt) in
       self.integralk_56 <- copy_85 ;
       (xk_59 , uk_58 , errork_55 , integralkm1_57))):float *
                                                      float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_64 : 'g ;
    mutable h_71 : 'f ;
    mutable i_69 : 'e ;
    mutable h_67 : 'd ;
    mutable result_66 : 'c ; mutable xk1_81 : 'b ; mutable integralk_77 : 'a }

let main (cstate_88:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_64 = false ;
      h_71 = 42. ;
      i_69 = (false:bool) ;
      h_67 = (42.:float) ;
      result_66 = (():unit) ;
      xk1_81 = (42.:float) ; integralk_77 = (42.:float) } in
  let main_step self ((time_63:float) , ()) =
    ((self.major_64 <- cstate_88.major ;
      (let (result_93:unit) =
           let h_70 = ref (infinity:float) in
           (if self.i_69 then self.h_67 <- (+.) time_63  0.) ;
           (let (z_68:bool) = (&&) self.major_64  ((>=) time_63  self.h_67) in
            self.h_67 <- (if z_68 then (+.) self.h_67  0.1 else self.h_67) ;
            h_70 := min !h_70  self.h_67 ;
            self.h_71 <- !h_70 ;
            self.i_69 <- false ;
            (let (trigger_65:zero) = z_68 in
             (begin match trigger_65 with
                    | true ->
                        let () = () in
                        let (l_83:float) = self.xk1_81 in
                        let ((xk_80:float): float) = l_83 in
                        let ((errork_76:float): float) = (-.) r  xk_80 in
                        let (l_82:float) = self.integralk_77 in
                        let ((integralkm1_78:float): float) = l_82 in
                        let ((uk_79:float): float) =
                            (+.) (( *. ) kp  errork_76) 
                                 (( *. ) ki  integralkm1_78) in
                        let ((copy_86:float): float) =
                            (+.) xk_80  (( *. ) uk_79  dt) in
                        self.xk1_81 <- copy_86 ;
                        (let ((copy_87:float): float) =
                             (+.) integralkm1_78  (( *. ) errork_76  dt) in
                         self.integralk_77 <- copy_87 ;
                         (let (integral_73:float) = integralkm1_78 in
                          let (error_72:float) = errork_76 in
                          let (u_74:float) = uk_79 in
                          let (x_75:float) = xk_80 in
                          let _ = print_float x_75 in
                          let _ = print_string "," in
                          let _ = print_float u_74 in
                          let _ = print_string "," in
                          let _ = print_float error_72 in
                          let _ = print_string "," in
                          let _ = print_float integral_73 in
                          self.result_66 <- print_newline ()))
                    | _ -> self.result_66 <- ()  end) ; self.result_66)) in
       cstate_88.horizon <- min cstate_88.horizon  self.h_71 ; result_93)):
    unit) in 
  let main_reset self  =
    ((self.i_69 <- true ; self.xk1_81 <- 0. ; self.integralk_77 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
