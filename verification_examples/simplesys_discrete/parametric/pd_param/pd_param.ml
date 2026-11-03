(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

let kd = 0.5

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_121 : 'e ;
    mutable xk1_116 : 'd ;
    mutable errork1_110 : 'c ;
    mutable energyk1_107 : 'b ; mutable derivativek1_104 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_121 = (false:bool) ;
      xk1_116 = (42.:float) ;
      errork1_110 = (42.:float) ;
      energyk1_107 = (42.:float) ; derivativek1_104 = (42.:float) } in
  let exec_reset self  =
    ((self.derivativek1_104 <- 0. ;
      self.errork1_110 <- 1. ; self.xk1_116 <- 0. ; self.i_121 <- true):
    unit) in 
  let exec_step self () =
    ((let (l_117:float) = self.derivativek1_104 in
      let ((derivativek_103:float): float) = l_117 in
      let (l_119:float) = self.errork1_110 in
      let ((errork_109:float): float) = l_119 in
      let ((uk_114:float): float) =
          (-.) (( *. ) kp  errork_109)  (( *. ) kd  derivativek_103) in
      let (l_120:float) = self.xk1_116 in
      let ((xk_115:float): float) = l_120 in
      let ((copy_159:float): float) = (+.) xk_115  (( *. ) uk_114  dt) in
      self.xk1_116 <- copy_159 ;
      (let ((copy_158:float): float) = (-.) r  self.xk1_116 in
       self.errork1_110 <- copy_158 ;
       (let ((copy_157:float): float) =
            (/.) ((-.) self.errork1_110  errork_109)  dt in
        self.derivativek1_104 <- copy_157 ;
        (let ((beta_102:float): float) =
             ( *. ) ((-.) 1.  (( *. ) kp  dt))  dt in
         let ((alpha_101:float): float) = kp in
         let ((copy_156:float): float) =
             (+.) (( *. ) (( *. ) alpha_101  self.errork1_110) 
                          self.errork1_110) 
                  (( *. ) (( *. ) beta_102  self.derivativek1_104) 
                          self.derivativek1_104) in
         (if self.i_121 then self.energyk1_107 <- alpha_101) ;
         (let (l_118:float) = self.energyk1_107 in
          self.energyk1_107 <- copy_156 ;
          self.i_121 <- false ;
          (let ((diffenergy_105:float): float) =
               (+.) ((-.) 0. 
                          (( *. ) (( *. ) (( *. ) (( *. ) kp  kp)  dt) 
                                          errork_109)  errork_109)) 
                    (( *. ) (( *. ) (( *. ) ((-.) ((+.) (( *. ) kd  kd) 
                                                        (( *. ) kp  dt))  
                                                  1.)  dt)  derivativek_103) 
                            derivativek_103) in
           let ((testenergy1_113:float): float) =
               ( *. ) (( *. ) alpha_101  errork_109)  errork_109 in
           let ((testbeta_112:float): float) = beta_102 in
           let ((testalpha_111:float): float) = alpha_101 in
           let ((energyk_106:float): float) = l_118 in
           let ((energykv2_108:float): float) = energyk_106 in
           (xk_115 , uk_114 , errork_109 , derivativek_103))))))):float *
                                                                  float *
                                                                  float *
                                                                  float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_123 : 'j ;
    mutable h_130 : 'i ;
    mutable i_128 : 'h ;
    mutable h_126 : 'g ;
    mutable result_125 : 'f ;
    mutable i_155 : 'e ;
    mutable xk1_150 : 'd ;
    mutable errork1_144 : 'c ;
    mutable energyk1_141 : 'b ; mutable derivativek1_138 : 'a }

let main (cstate_164:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_123 = false ;
      h_130 = 42. ;
      i_128 = (false:bool) ;
      h_126 = (42.:float) ;
      result_125 = (():unit) ;
      i_155 = (false:bool) ;
      xk1_150 = (42.:float) ;
      errork1_144 = (42.:float) ;
      energyk1_141 = (42.:float) ; derivativek1_138 = (42.:float) } in
  let main_step self ((time_122:float) , ()) =
    ((self.major_123 <- cstate_164.major ;
      (let (result_169:unit) =
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
                        let ((alpha_135:float): float) = kp in
                        (if self.i_155 then self.energyk1_141 <- alpha_135) ;
                        self.i_155 <- false ;
                        (let () = () in
                         let (l_151:float) = self.derivativek1_138 in
                         let ((derivativek_137:float): float) = l_151 in
                         let (l_153:float) = self.errork1_144 in
                         let ((errork_143:float): float) = l_153 in
                         let ((uk_148:float): float) =
                             (-.) (( *. ) kp  errork_143) 
                                  (( *. ) kd  derivativek_137) in
                         let (l_154:float) = self.xk1_150 in
                         let ((xk_149:float): float) = l_154 in
                         let ((copy_163:float): float) =
                             (+.) xk_149  (( *. ) uk_148  dt) in
                         self.xk1_150 <- copy_163 ;
                         (let ((copy_162:float): float) =
                              (-.) r  self.xk1_150 in
                          self.errork1_144 <- copy_162 ;
                          (let ((copy_161:float): float) =
                               (/.) ((-.) self.errork1_144  errork_143)  dt in
                           self.derivativek1_138 <- copy_161 ;
                           (let ((beta_136:float): float) =
                                ( *. ) ((-.) 1.  (( *. ) kp  dt))  dt in
                            let ((copy_160:float): float) =
                                (+.) (( *. ) (( *. ) alpha_135 
                                                     self.errork1_144) 
                                             self.errork1_144) 
                                     (( *. ) (( *. ) beta_136 
                                                     self.derivativek1_138) 
                                             self.derivativek1_138) in
                            let (l_152:float) = self.energyk1_141 in
                            self.energyk1_141 <- copy_160 ;
                            (let ((diffenergy_139:float): float) =
                                 (+.) ((-.) 0. 
                                            (( *. ) (( *. ) (( *. ) (
                                                                    ( *. ) 
                                                                    kp  kp) 
                                                                    dt) 
                                                            errork_143) 
                                                    errork_143)) 
                                      (( *. ) (( *. ) (( *. ) ((-.) (
                                                                    (+.) 
                                                                    (
                                                                    ( *. ) 
                                                                    kd  kd) 
                                                                    (
                                                                    ( *. ) 
                                                                    kp  dt)) 
                                                                    1.)  
                                                              dt) 
                                                      derivativek_137) 
                                              derivativek_137) in
                             let ((testenergy1_147:float): float) =
                                 ( *. ) (( *. ) alpha_135  errork_143) 
                                        errork_143 in
                             let ((testbeta_146:float): float) = beta_136 in
                             let ((testalpha_145:float): float) = alpha_135 in
                             let ((energyk_140:float): float) = l_152 in
                             let ((energykv2_142:float): float) = energyk_140 in
                             let (derivativek_131:float) = derivativek_137 in
                             let (errork_132:float) = errork_143 in
                             let (uk_133:float) = uk_148 in
                             let (xk_134:float) = xk_149 in
                             let _ = print_float xk_134 in
                             let _ = print_string "," in
                             let _ = print_float uk_133 in
                             let _ = print_string "," in
                             let _ = print_float errork_132 in
                             let _ = print_string "," in
                             let _ = print_float derivativek_131 in
                             self.result_125 <- print_newline ())))))
                    | _ -> self.result_125 <- ()  end) ; self.result_125)) in
       cstate_164.horizon <- min cstate_164.horizon  self.h_130 ; result_169)):
    unit) in 
  let main_reset self  =
    ((self.i_128 <- true ;
      self.i_155 <- true ;
      self.derivativek1_138 <- 0. ;
      self.errork1_144 <- 1. ; self.xk1_150 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
