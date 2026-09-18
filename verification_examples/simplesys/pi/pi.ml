(* The Zelus compiler, version 2.2-dev
  (2026-09-8-16:32) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let dt = 0.1

type ('d , 'c , 'b , 'a) _exec =
  { mutable i_121 : 'd ;
    mutable m_119 : 'c ; mutable xk1_116 : 'b ; mutable integralk1_113 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_121 = (false:bool) ;
      m_119 = (42.:float) ;
      xk1_116 = (42.:float) ; integralk1_113 = (42.:float) } in
  let exec_reset self  =
    ((self.i_121 <- true ; self.integralk1_113 <- 0. ; self.xk1_116 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_117:float) = self.integralk1_113 in
      let ((integralk_112:float): float) = l_117 in
      let (l_118:float) = self.xk1_116 in
      let ((xk_115:float): float) = l_118 in
      let ((errork_110:float): float) = (-.) r  xk_115 in
      let ((energyk_107:float): float) =
          (+.) (( *. ) (( *. ) 0.99  errork_110)  errork_110) 
               (( *. ) (( *. ) 1.  integralk_112)  integralk_112) in
      (if self.i_121 then self.m_119 <- energyk_107) ;
      self.i_121 <- false ;
      (let (next_120:float) = self.m_119 in
       let ((energy0_105:float): float) = next_120 in
       let ((energybound_106:float): float) = (-.) energyk_107  energy0_105 in
       self.m_119 <- 0. ;
       (let ((en0_104:float): float) =
            (+.) (( *. ) (( *. ) 0.99  1.)  1.)  (( *. ) (( *. ) 1.  0.)  0.) in
        let ((uk_114:float): float) =
            (+.) (( *. ) kp  errork_110)  (( *. ) ki  integralk_112) in
        let ((copy_157:float): float) = (+.) xk_115  (( *. ) uk_114  dt) in
        self.xk1_116 <- copy_157 ;
        (let ((errork1_111:float): float) = (-.) r  self.xk1_116 in
         let ((copy_156:float): float) =
             (+.) integralk_112  (( *. ) errork1_111  dt) in
         self.integralk1_113 <- copy_156 ;
         (let ((energyk1_108:float): float) =
              (+.) (( *. ) (( *. ) 0.99  errork1_111)  errork1_111) 
                   (( *. ) (( *. ) 1.  self.integralk1_113) 
                           self.integralk1_113) in
          let ((engerydec_109:float): float) = (-.) energyk1_108  energyk_107 in
          let ((diffenergy3_103:float): float) =
              (-.) (( *. ) (( *. ) (-0.35)  errork_110)  errork_110) 
                   (( *. ) (( *. ) 0.01  integralk_112)  integralk_112) in
          let ((diffenergy2_102:float): float) =
              (-.) ((+.) (( *. ) (( *. ) 0.99 
                                         ((-.) (( *. ) 0.8  errork_110) 
                                               (( *. ) 0.1  integralk_112))) 
                                 ((-.) (( *. ) 0.8  errork_110) 
                                       (( *. ) 0.1  integralk_112))) 
                         (( *. ) (( *. ) 1. 
                                         ((+.) (( *. ) 0.08  errork_110) 
                                               (( *. ) 0.99  integralk_112)))
                                 
                                 ((+.) (( *. ) 0.08  errork_110) 
                                       (( *. ) 0.99  integralk_112)))) 
                   ((+.) (( *. ) (( *. ) 0.99  errork_110)  errork_110) 
                         (( *. ) (( *. ) 1.  integralk_112)  integralk_112)) in
          let ((diffenergy1_101:float): float) =
              (-.) ((+.) (( *. ) (( *. ) 0.99  errork1_111)  errork1_111) 
                         (( *. ) (( *. ) 1.  self.integralk1_113) 
                                 self.integralk1_113)) 
                   ((+.) (( *. ) (( *. ) 0.99  errork_110)  errork_110) 
                         (( *. ) (( *. ) 1.  integralk_112)  integralk_112)) in
          (xk_115 , uk_114 , errork_110 , integralk_112)))))):float *
                                                              float *
                                                              float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_123 : 'i ;
    mutable h_130 : 'h ;
    mutable i_128 : 'g ;
    mutable h_126 : 'f ;
    mutable result_125 : 'e ;
    mutable i_155 : 'd ;
    mutable m_153 : 'c ; mutable xk1_150 : 'b ; mutable integralk1_147 : 'a }

let main (cstate_160:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_123 = false ;
      h_130 = 42. ;
      i_128 = (false:bool) ;
      h_126 = (42.:float) ;
      result_125 = (():unit) ;
      i_155 = (false:bool) ;
      m_153 = (42.:float) ;
      xk1_150 = (42.:float) ; integralk1_147 = (42.:float) } in
  let main_step self ((time_122:float) , ()) =
    ((self.major_123 <- cstate_160.major ;
      (let (result_165:unit) =
           let h_129 = ref (infinity:float) in
           (if self.i_128 then self.h_126 <- (+.) time_122  0.) ;
           (let (z_127:bool) =
                (&&) self.major_123  ((>=) time_122  self.h_126) in
            self.h_126 <- (if z_127 then (+.) self.h_126  0.1 else self.h_126)
            ;
            h_129 := min !h_129  self.h_126 ;
            self.h_130 <- !h_129 ;
            self.i_128 <- false ;
            (let (trigger_124:zero) = z_127 in
             (begin match trigger_124 with
                    | true ->
                        let (l_151:float) = self.integralk1_147 in
                        let ((integralk_146:float): float) = l_151 in
                        let (l_152:float) = self.xk1_150 in
                        let ((xk_149:float): float) = l_152 in
                        let ((errork_144:float): float) = (-.) r  xk_149 in
                        let ((energyk_141:float): float) =
                            (+.) (( *. ) (( *. ) 0.99  errork_144) 
                                         errork_144) 
                                 (( *. ) (( *. ) 1.  integralk_146) 
                                         integralk_146) in
                        (if self.i_155 then self.m_153 <- energyk_141) ;
                        self.i_155 <- false ;
                        (let () = () in
                         let (next_154:float) = self.m_153 in
                         let ((energy0_139:float): float) = next_154 in
                         let ((energybound_140:float): float) =
                             (-.) energyk_141  energy0_139 in
                         self.m_153 <- 0. ;
                         (let ((en0_138:float): float) =
                              (+.) (( *. ) (( *. ) 0.99  1.)  1.) 
                                   (( *. ) (( *. ) 1.  0.)  0.) in
                          let ((uk_148:float): float) =
                              (+.) (( *. ) kp  errork_144) 
                                   (( *. ) ki  integralk_146) in
                          let ((copy_159:float): float) =
                              (+.) xk_149  (( *. ) uk_148  dt) in
                          self.xk1_150 <- copy_159 ;
                          (let ((errork1_145:float): float) =
                               (-.) r  self.xk1_150 in
                           let ((copy_158:float): float) =
                               (+.) integralk_146  (( *. ) errork1_145  dt) in
                           self.integralk1_147 <- copy_158 ;
                           (let ((energyk1_142:float): float) =
                                (+.) (( *. ) (( *. ) 0.99  errork1_145) 
                                             errork1_145) 
                                     (( *. ) (( *. ) 1.  self.integralk1_147)
                                              self.integralk1_147) in
                            let ((engerydec_143:float): float) =
                                (-.) energyk1_142  energyk_141 in
                            let ((diffenergy3_137:float): float) =
                                (-.) (( *. ) (( *. ) (-0.35)  errork_144) 
                                             errork_144) 
                                     (( *. ) (( *. ) 0.01  integralk_146) 
                                             integralk_146) in
                            let ((diffenergy2_136:float): float) =
                                (-.) ((+.) (( *. ) (( *. ) 0.99 
                                                           ((-.) (( *. ) 
                                                                    0.8 
                                                                    errork_144)
                                                                 
                                                                 (( *. ) 
                                                                    0.1 
                                                                    integralk_146)))
                                                   
                                                   ((-.) (( *. ) 0.8 
                                                                 errork_144) 
                                                         (( *. ) 0.1 
                                                                 integralk_146)))
                                           
                                           (( *. ) (( *. ) 1. 
                                                           ((+.) (( *. ) 
                                                                    0.08 
                                                                    errork_144)
                                                                 
                                                                 (( *. ) 
                                                                    0.99 
                                                                    integralk_146)))
                                                   
                                                   ((+.) (( *. ) 0.08 
                                                                 errork_144) 
                                                         (( *. ) 0.99 
                                                                 integralk_146))))
                                     
                                     ((+.) (( *. ) (( *. ) 0.99  errork_144) 
                                                   errork_144) 
                                           (( *. ) (( *. ) 1.  integralk_146)
                                                    integralk_146)) in
                            let ((diffenergy1_135:float): float) =
                                (-.) ((+.) (( *. ) (( *. ) 0.99  errork1_145)
                                                    errork1_145) 
                                           (( *. ) (( *. ) 1. 
                                                           self.integralk1_147)
                                                    self.integralk1_147)) 
                                     ((+.) (( *. ) (( *. ) 0.99  errork_144) 
                                                   errork_144) 
                                           (( *. ) (( *. ) 1.  integralk_146)
                                                    integralk_146)) in
                            let (integral_132:float) = integralk_146 in
                            let (error_131:float) = errork_144 in
                            let (u_133:float) = uk_148 in
                            let (x_134:float) = xk_149 in
                            let _ = print_float x_134 in
                            let _ = print_string "," in
                            let _ = print_float u_133 in
                            let _ = print_string "," in
                            let _ = print_float error_131 in
                            let _ = print_string "," in
                            let _ = print_float integral_132 in
                            self.result_125 <- print_newline ()))))
                    | _ -> self.result_125 <- ()  end) ; self.result_125)) in
       cstate_160.horizon <- min cstate_160.horizon  self.h_130 ; result_165)):
    unit) in 
  let main_reset self  =
    ((self.i_128 <- true ;
      self.i_155 <- true ; self.integralk1_147 <- 0. ; self.xk1_150 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
