(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let r = 1.

let kp = 10.

let ki = 0.5

let kd = 0.5

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable xk1_85 : 'c ; mutable integralk1_82 : 'b ; mutable errork_78 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_85 = (42.:float) ;
      integralk1_82 = (42.:float) ; errork_78 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_85 <- 0. ; self.errork_78 <- 1. ; self.integralk1_82 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_88:float) = self.xk1_85 in
      let ((xk_84:float): float) = l_88 in
      let ((copy_118:float): float) = (-.) r  xk_84 in
      let (l_86:float) = self.errork_78 in
      self.errork_78 <- copy_118 ;
      (let ((errorkm1_80:float): float) = l_86 in
       let ((derivativek_76:float): float) =
           (/.) ((-.) self.errork_78  errorkm1_80)  dt in
       let (l_87:float) = self.integralk1_82 in
       let ((integralk_81:float): float) = l_87 in
       let ((uk_83:float): float) =
           (-.) ((+.) (( *. ) kp  self.errork_78)  (( *. ) ki  integralk_81))
                 (( *. ) kd  derivativek_76) in
       let ((copy_117:float): float) = (+.) xk_84  (( *. ) uk_83  dt) in
       self.xk1_85 <- copy_117 ;
       (let ((errork1_79:float): float) = (-.) r  self.xk1_85 in
        let ((copy_116:float): float) =
            (+.) integralk_81  (( *. ) errork1_79  dt) in
        self.integralk1_82 <- copy_116 ;
        (let ((derivativek1_77:float): float) =
             (/.) ((-.) errork1_79  self.errork_78)  dt in
         (xk_84 , uk_83 , self.errork_78 , integralk_81 , derivativek_76))))):
    float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_90 : 'h ;
    mutable h_97 : 'g ;
    mutable i_95 : 'f ;
    mutable h_93 : 'e ;
    mutable result_92 : 'd ;
    mutable xk1_112 : 'c ;
    mutable integralk1_109 : 'b ; mutable errork_105 : 'a }

let main (cstate_122:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_90 = false ;
      h_97 = 42. ;
      i_95 = (false:bool) ;
      h_93 = (42.:float) ;
      result_92 = (():unit) ;
      xk1_112 = (42.:float) ;
      integralk1_109 = (42.:float) ; errork_105 = (42.:float) } in
  let main_step self ((time_89:float) , ()) =
    ((self.major_90 <- cstate_122.major ;
      (let (result_127:unit) =
           let h_96 = ref (infinity:float) in
           (if self.i_95 then self.h_93 <- (+.) time_89  0.) ;
           (let (z_94:bool) = (&&) self.major_90  ((>=) time_89  self.h_93) in
            self.h_93 <- (if z_94 then (+.) self.h_93  0.1 else self.h_93) ;
            h_96 := min !h_96  self.h_93 ;
            self.h_97 <- !h_96 ;
            self.i_95 <- false ;
            (let (trigger_91:zero) = z_94 in
             (begin match trigger_91 with
                    | true ->
                        let () = () in
                        let (l_115:float) = self.xk1_112 in
                        let ((xk_111:float): float) = l_115 in
                        let ((copy_121:float): float) = (-.) r  xk_111 in
                        let (l_113:float) = self.errork_105 in
                        self.errork_105 <- copy_121 ;
                        (let ((errorkm1_107:float): float) = l_113 in
                         let ((derivativek_103:float): float) =
                             (/.) ((-.) self.errork_105  errorkm1_107)  dt in
                         let (l_114:float) = self.integralk1_109 in
                         let ((integralk_108:float): float) = l_114 in
                         let ((uk_110:float): float) =
                             (-.) ((+.) (( *. ) kp  self.errork_105) 
                                        (( *. ) ki  integralk_108)) 
                                  (( *. ) kd  derivativek_103) in
                         let ((copy_120:float): float) =
                             (+.) xk_111  (( *. ) uk_110  dt) in
                         self.xk1_112 <- copy_120 ;
                         (let ((errork1_106:float): float) =
                              (-.) r  self.xk1_112 in
                          let ((copy_119:float): float) =
                              (+.) integralk_108  (( *. ) errork1_106  dt) in
                          self.integralk1_109 <- copy_119 ;
                          (let ((derivativek1_104:float): float) =
                               (/.) ((-.) errork1_106  self.errork_105)  dt in
                           let (derivativek_98:float) = derivativek_103 in
                           let (integralk_100:float) = integralk_108 in
                           let (errork_99:float) = self.errork_105 in
                           let (uk_101:float) = uk_110 in
                           let (xk_102:float) = xk_111 in
                           let _ = print_float xk_102 in
                           let _ = print_string "," in
                           let _ = print_float uk_101 in
                           let _ = print_string "," in
                           let _ = print_float errork_99 in
                           let _ = print_string "," in
                           let _ = print_float integralk_100 in
                           let _ = print_string "," in
                           let _ = print_float derivativek_98 in
                           self.result_92 <- print_newline ())))
                    | _ -> self.result_92 <- ()  end) ; self.result_92)) in
       cstate_122.horizon <- min cstate_122.horizon  self.h_97 ; result_127)):
    unit) in 
  let main_reset self  =
    ((self.i_95 <- true ;
      self.xk1_112 <- 0. ; self.errork_105 <- 1. ; self.integralk1_109 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
