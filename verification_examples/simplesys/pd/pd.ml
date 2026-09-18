(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let kp = 2.

let kd = 0.5

let dt = 0.1

type ('b , 'a) _exec =
  { mutable xk1_85 : 'b ; mutable errork_80 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();{ xk1_85 = (42.:float) ; errork_80 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_85 <- 0. ; self.errork_80 <- 1.):unit) in 
  let exec_step self () =
    ((let (l_87:float) = self.xk1_85 in
      let ((xk_84:float): float) = l_87 in
      let ((copy_115:float): float) = (-.) r  xk_84 in
      let (l_86:float) = self.errork_80 in
      self.errork_80 <- copy_115 ;
      (let ((errorkm1_82:float): float) = l_86 in
       let ((derivativek_75:float): float) =
           (/.) ((-.) self.errork_80  errorkm1_82)  dt in
       let ((diffenergy3_77:float): float) =
           (-.) (( *. ) (( *. ) (-0.2)  self.errork_80)  self.errork_80) 
                (( *. ) (( *. ) 0.0275  derivativek_75)  derivativek_75) in
       let ((uk_83:float): float) =
           (-.) (( *. ) kp  self.errork_80)  (( *. ) kd  derivativek_75) in
       let ((copy_114:float): float) = (+.) xk_84  (( *. ) uk_83  dt) in
       self.xk1_85 <- copy_114 ;
       (let ((errork1_81:float): float) = (-.) r  self.xk1_85 in
        let ((derivativek1_76:float): float) =
            (/.) ((-.) errork1_81  self.errork_80)  dt in
        let ((energyk1_79:float): float) =
            (+.) (( *. ) errork1_81  errork1_81) 
                 (( *. ) (( *. ) 0.04  derivativek1_76)  derivativek1_76) in
        let ((energyk_78:float): float) =
            (+.) (( *. ) self.errork_80  self.errork_80) 
                 (( *. ) (( *. ) 0.04  derivativek_75)  derivativek_75) in
        (xk_84 , uk_83 , self.errork_80 , derivativek_75)))):float *
                                                             float *
                                                             float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_89 : 'g ;
    mutable h_96 : 'f ;
    mutable i_94 : 'e ;
    mutable h_92 : 'd ;
    mutable result_91 : 'c ; mutable xk1_111 : 'b ; mutable errork_106 : 'a }

let main (cstate_118:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_89 = false ;
      h_96 = 42. ;
      i_94 = (false:bool) ;
      h_92 = (42.:float) ;
      result_91 = (():unit) ;
      xk1_111 = (42.:float) ; errork_106 = (42.:float) } in
  let main_step self ((time_88:float) , ()) =
    ((self.major_89 <- cstate_118.major ;
      (let (result_123:unit) =
           let h_95 = ref (infinity:float) in
           (if self.i_94 then self.h_92 <- (+.) time_88  0.) ;
           (let (z_93:bool) = (&&) self.major_89  ((>=) time_88  self.h_92) in
            self.h_92 <- (if z_93 then (+.) self.h_92  0.1 else self.h_92) ;
            h_95 := min !h_95  self.h_92 ;
            self.h_96 <- !h_95 ;
            self.i_94 <- false ;
            (let (trigger_90:zero) = z_93 in
             (begin match trigger_90 with
                    | true ->
                        let () = () in
                        let (l_113:float) = self.xk1_111 in
                        let ((xk_110:float): float) = l_113 in
                        let ((copy_117:float): float) = (-.) r  xk_110 in
                        let (l_112:float) = self.errork_106 in
                        self.errork_106 <- copy_117 ;
                        (let ((errorkm1_108:float): float) = l_112 in
                         let ((derivativek_101:float): float) =
                             (/.) ((-.) self.errork_106  errorkm1_108)  dt in
                         let ((diffenergy3_103:float): float) =
                             (-.) (( *. ) (( *. ) (-0.2)  self.errork_106) 
                                          self.errork_106) 
                                  (( *. ) (( *. ) 0.0275  derivativek_101) 
                                          derivativek_101) in
                         let ((uk_109:float): float) =
                             (-.) (( *. ) kp  self.errork_106) 
                                  (( *. ) kd  derivativek_101) in
                         let ((copy_116:float): float) =
                             (+.) xk_110  (( *. ) uk_109  dt) in
                         self.xk1_111 <- copy_116 ;
                         (let ((errork1_107:float): float) =
                              (-.) r  self.xk1_111 in
                          let ((derivativek1_102:float): float) =
                              (/.) ((-.) errork1_107  self.errork_106)  dt in
                          let ((energyk1_105:float): float) =
                              (+.) (( *. ) errork1_107  errork1_107) 
                                   (( *. ) (( *. ) 0.04  derivativek1_102) 
                                           derivativek1_102) in
                          let ((energyk_104:float): float) =
                              (+.) (( *. ) self.errork_106  self.errork_106) 
                                   (( *. ) (( *. ) 0.04  derivativek_101) 
                                           derivativek_101) in
                          let (derivative_97:float) = derivativek_101 in
                          let (error_98:float) = self.errork_106 in
                          let (u_99:float) = uk_109 in
                          let (x_100:float) = xk_110 in
                          let _ = print_float x_100 in
                          let _ = print_string "," in
                          let _ = print_float u_99 in
                          let _ = print_string "," in
                          let _ = print_float error_98 in
                          let _ = print_string "," in
                          let _ = print_float derivative_97 in
                          self.result_91 <- print_newline ()))
                    | _ -> self.result_91 <- ()  end) ; self.result_91)) in
       cstate_118.horizon <- min cstate_118.horizon  self.h_96 ; result_123)):
    unit) in 
  let main_reset self  =
    ((self.i_94 <- true ; self.xk1_111 <- 0. ; self.errork_106 <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
