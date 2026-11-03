(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let kd = 0.5

let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable xk1_149 : 'e ;
    mutable integralk1_144 : 'd ;
    mutable errork1_139 : 'c ;
    mutable energyk1_135 : 'b ; mutable derivativek1_129 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_149 = (42.:float) ;
      integralk1_144 = (42.:float) ;
      errork1_139 = (42.:float) ;
      energyk1_135 = (42.:float) ; derivativek1_129 = (42.:float) } in
  let exec_reset self  =
    ((self.derivativek1_129 <- 0. ;
      self.integralk1_144 <- 0. ;
      self.errork1_139 <- 1. ;
      self.xk1_149 <- 0. ; self.energyk1_135 <- 1.1375):unit) in 
  let exec_step self () =
    ((let (l_150:float) = self.derivativek1_129 in
      let ((derivativek_128:float): float) = l_150 in
      let (l_153:float) = self.integralk1_144 in
      let ((integralk_143:float): float) = l_153 in
      let (l_152:float) = self.errork1_139 in
      let ((errork_138:float): float) = l_152 in
      let ((uk_147:float): float) =
          (-.) ((+.) (( *. ) kp  errork_138)  (( *. ) ki  integralk_143)) 
               (( *. ) kd  derivativek_128) in
      let (l_154:float) = self.xk1_149 in
      let ((xk_148:float): float) = l_154 in
      let ((copy_200:float): float) = (+.) xk_148  (( *. ) uk_147  dt) in
      self.xk1_149 <- copy_200 ;
      (let ((copy_199:float): float) = (-.) r  self.xk1_149 in
       self.errork1_139 <- copy_199 ;
       (let ((copy_198:float): float) =
            (+.) integralk_143  (( *. ) self.errork1_139  dt) in
        self.integralk1_144 <- copy_198 ;
        (let ((copy_197:float): float) =
             (/.) ((-.) self.errork1_139  errork_138)  dt in
         self.derivativek1_129 <- copy_197 ;
         (let ((copy_196:float): float) =
              (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375  self.errork1_139) 
                                       self.errork1_139) 
                               (( *. ) (( *. ) 1.25  self.integralk1_144) 
                                       self.integralk1_144)) 
                         (( *. ) (( *. ) 0.05  self.derivativek1_129) 
                                 self.derivativek1_129)) 
                   (( *. ) (( *. ) 1.  self.errork1_139)  self.integralk1_144) in
          let (l_151:float) = self.energyk1_135 in
          self.energyk1_135 <- copy_196 ;
          (let ((energyk_134:float): float) = l_151 in
           let ((diffhelp_133:float): float) =
               (-.) self.energyk1_135  energyk_134 in
           let ((errork1integralk1help_142:float): float) =
               (+.) ((+.) ((+.) ((-.) ((-.) ((-.) ((+.) ((+.) (( *. ) 
                                                                 (( *. ) 
                                                                    0.064 
                                                                    errork_138)
                                                                  errork_138)
                                                              
                                                              (( *. ) 
                                                                 (( *. ) 
                                                                    0.792 
                                                                    errork_138)
                                                                 
                                                                 integralk_143))
                                                        
                                                        (( *. ) (( *. ) 
                                                                   0.004 
                                                                   errork_138)
                                                                
                                                                derivativek_128))
                                                  
                                                  (( *. ) (( *. ) 0.008 
                                                                  errork_138)
                                                           integralk_143)) 
                                            (( *. ) (( *. ) 0.099 
                                                            integralk_143) 
                                                    integralk_143)) 
                                      (( *. ) (( *. ) 0.0005  integralk_143) 
                                              derivativek_128)) 
                                (( *. ) (( *. ) 0.004  errork_138) 
                                        derivativek_128)) 
                          (( *. ) (( *. ) 0.0495  integralk_143) 
                                  derivativek_128)) 
                    (( *. ) (( *. ) 0.00025  derivativek_128) 
                            derivativek_128) in
           let ((derivativek1help2_131:float): float) =
               (-.) ((-.) ((+.) ((+.) ((+.) (( *. ) (( *. ) 4.  errork_138) 
                                                    errork_138) 
                                            (( *. ) (( *. ) 1.  integralk_143)
                                                     integralk_143)) 
                                      (( *. ) (( *. ) 0.25  derivativek_128) 
                                              derivativek_128)) 
                                (( *. ) (( *. ) 4.  errork_138) 
                                        integralk_143)) 
                          (( *. ) (( *. ) 2.  errork_138)  derivativek_128)) 
                    (( *. ) (( *. ) 1.  integralk_143)  derivativek_128) in
           let ((integralk1help2_146:float): float) =
               (+.) ((+.) ((+.) ((+.) ((+.) (( *. ) (( *. ) 0.0064 
                                                            errork_138) 
                                                    errork_138) 
                                            (( *. ) (( *. ) 0.9801 
                                                            integralk_143) 
                                                    integralk_143)) 
                                      (( *. ) (( *. ) 2.5e-05 
                                                      derivativek_128) 
                                              derivativek_128)) 
                                (( *. ) (( *. ) 0.1584  errork_138) 
                                        integralk_143)) 
                          (( *. ) (( *. ) 0.0008  errork_138) 
                                  derivativek_128)) 
                    (( *. ) (( *. ) 0.0099  integralk_143)  derivativek_128) in
           let ((errork1help2_141:float): float) =
               (-.) ((+.) ((-.) ((+.) ((+.) (( *. ) (( *. ) 0.64  errork_138)
                                                     errork_138) 
                                            (( *. ) (( *. ) 0.01 
                                                            integralk_143) 
                                                    integralk_143)) 
                                      (( *. ) (( *. ) 0.0025  derivativek_128)
                                               derivativek_128)) 
                                (( *. ) (( *. ) 0.16  errork_138) 
                                        integralk_143)) 
                          (( *. ) (( *. ) 0.08  errork_138)  derivativek_128))
                     (( *. ) (( *. ) 0.01  integralk_143)  derivativek_128) in
           let ((energyk1v2_136:float): float) = self.energyk1_135 in
           let ((derivativek1help_130:float): float) =
               (+.) ((-.) (( *. ) (-2.)  errork_138)  integralk_143) 
                    (( *. ) 0.5  derivativek_128) in
           let ((integralk1help_145:float): float) =
               (+.) ((+.) (( *. ) 0.08  errork_138) 
                          (( *. ) 0.99  integralk_143)) 
                    (( *. ) 0.005  derivativek_128) in
           let ((errork1help_140:float): float) =
               (+.) ((-.) (( *. ) 0.8  errork_138) 
                          (( *. ) 0.1  integralk_143)) 
                    (( *. ) 0.05  derivativek_128) in
           let ((diffenergy1_132:float): float) =
               (-.) ((+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375 
                                                      self.errork1_139) 
                                              self.errork1_139) 
                                      (( *. ) (( *. ) 1.25 
                                                      self.integralk1_144) 
                                              self.integralk1_144)) 
                                (( *. ) (( *. ) 0.05  self.derivativek1_129) 
                                        self.derivativek1_129)) 
                          (( *. ) (( *. ) 1.  self.errork1_139) 
                                  self.integralk1_144)) 
                    ((+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375  errork_138) 
                                              errork_138) 
                                      (( *. ) (( *. ) 1.25  integralk_143) 
                                              integralk_143)) 
                                (( *. ) (( *. ) 0.05  derivativek_128) 
                                        derivativek_128)) 
                          (( *. ) (( *. ) 1.  errork_138)  integralk_143)) in
           let ((energykv2_137:float): float) = energyk_134 in
           (xk_148 , uk_147 , errork_138 , integralk_143 , derivativek_128))))))):
    float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_156 : 'j ;
    mutable h_163 : 'i ;
    mutable i_161 : 'h ;
    mutable h_159 : 'g ;
    mutable result_158 : 'f ;
    mutable xk1_190 : 'e ;
    mutable integralk1_185 : 'd ;
    mutable errork1_180 : 'c ;
    mutable energyk1_176 : 'b ; mutable derivativek1_170 : 'a }

let main (cstate_206:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_156 = false ;
      h_163 = 42. ;
      i_161 = (false:bool) ;
      h_159 = (42.:float) ;
      result_158 = (():unit) ;
      xk1_190 = (42.:float) ;
      integralk1_185 = (42.:float) ;
      errork1_180 = (42.:float) ;
      energyk1_176 = (42.:float) ; derivativek1_170 = (42.:float) } in
  let main_step self ((time_155:float) , ()) =
    ((self.major_156 <- cstate_206.major ;
      (let (result_211:unit) =
           let h_162 = ref (infinity:float) in
           (if self.i_161 then self.h_159 <- (+.) time_155  0.) ;
           (let (z_160:bool) =
                (&&) self.major_156  ((>=) time_155  self.h_159) in
            self.h_159 <- (if z_160 then (+.) self.h_159  0.1 else self.h_159)
            ;
            h_162 := min !h_162  self.h_159 ;
            self.h_163 <- !h_162 ;
            self.i_161 <- false ;
            (let (trigger_157:zero) = z_160 in
             (begin match trigger_157 with
                    | true ->
                        let () = () in
                        let (l_191:float) = self.derivativek1_170 in
                        let ((derivativek_169:float): float) = l_191 in
                        let (l_194:float) = self.integralk1_185 in
                        let ((integralk_184:float): float) = l_194 in
                        let (l_193:float) = self.errork1_180 in
                        let ((errork_179:float): float) = l_193 in
                        let ((uk_188:float): float) =
                            (-.) ((+.) (( *. ) kp  errork_179) 
                                       (( *. ) ki  integralk_184)) 
                                 (( *. ) kd  derivativek_169) in
                        let (l_195:float) = self.xk1_190 in
                        let ((xk_189:float): float) = l_195 in
                        let ((copy_205:float): float) =
                            (+.) xk_189  (( *. ) uk_188  dt) in
                        self.xk1_190 <- copy_205 ;
                        (let ((copy_204:float): float) = (-.) r  self.xk1_190 in
                         self.errork1_180 <- copy_204 ;
                         (let ((copy_203:float): float) =
                              (+.) integralk_184 
                                   (( *. ) self.errork1_180  dt) in
                          self.integralk1_185 <- copy_203 ;
                          (let ((copy_202:float): float) =
                               (/.) ((-.) self.errork1_180  errork_179)  dt in
                           self.derivativek1_170 <- copy_202 ;
                           (let ((copy_201:float): float) =
                                (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375 
                                                                 self.errork1_180)
                                                          self.errork1_180) 
                                                 (( *. ) (( *. ) 1.25 
                                                                 self.integralk1_185)
                                                          self.integralk1_185))
                                           
                                           (( *. ) (( *. ) 0.05 
                                                           self.derivativek1_170)
                                                    self.derivativek1_170)) 
                                     (( *. ) (( *. ) 1.  self.errork1_180) 
                                             self.integralk1_185) in
                            let (l_192:float) = self.energyk1_176 in
                            self.energyk1_176 <- copy_201 ;
                            (let ((energyk_175:float): float) = l_192 in
                             let ((diffhelp_174:float): float) =
                                 (-.) self.energyk1_176  energyk_175 in
                             let ((errork1integralk1help_183:float): float) =
                                 (+.) ((+.) ((+.) ((-.) ((-.) ((-.) (
                                                                    (+.) 
                                                                    (
                                                                    (+.) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.064 
                                                                    errork_179)
                                                                    
                                                                    errork_179)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.792 
                                                                    errork_179)
                                                                    
                                                                    integralk_184))
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.004 
                                                                    errork_179)
                                                                    
                                                                    derivativek_169))
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.008 
                                                                    errork_179)
                                                                    
                                                                    integralk_184))
                                                              
                                                              (( *. ) 
                                                                 (( *. ) 
                                                                    0.099 
                                                                    integralk_184)
                                                                 
                                                                 integralk_184))
                                                        
                                                        (( *. ) (( *. ) 
                                                                   0.0005 
                                                                   integralk_184)
                                                                
                                                                derivativek_169))
                                                  
                                                  (( *. ) (( *. ) 0.004 
                                                                  errork_179)
                                                           derivativek_169)) 
                                            (( *. ) (( *. ) 0.0495 
                                                            integralk_184) 
                                                    derivativek_169)) 
                                      (( *. ) (( *. ) 0.00025 
                                                      derivativek_169) 
                                              derivativek_169) in
                             let ((derivativek1help2_172:float): float) =
                                 (-.) ((-.) ((+.) ((+.) ((+.) (( *. ) 
                                                                 (( *. ) 
                                                                    4. 
                                                                    errork_179)
                                                                  errork_179)
                                                              
                                                              (( *. ) 
                                                                 (( *. ) 
                                                                    1. 
                                                                    integralk_184)
                                                                 
                                                                 integralk_184))
                                                        
                                                        (( *. ) (( *. ) 
                                                                   0.25 
                                                                   derivativek_169)
                                                                
                                                                derivativek_169))
                                                  
                                                  (( *. ) (( *. ) 4. 
                                                                  errork_179)
                                                           integralk_184)) 
                                            (( *. ) (( *. ) 2.  errork_179) 
                                                    derivativek_169)) 
                                      (( *. ) (( *. ) 1.  integralk_184) 
                                              derivativek_169) in
                             let ((integralk1help2_187:float): float) =
                                 (+.) ((+.) ((+.) ((+.) ((+.) (( *. ) 
                                                                 (( *. ) 
                                                                    0.0064 
                                                                    errork_179)
                                                                  errork_179)
                                                              
                                                              (( *. ) 
                                                                 (( *. ) 
                                                                    0.9801 
                                                                    integralk_184)
                                                                 
                                                                 integralk_184))
                                                        
                                                        (( *. ) (( *. ) 
                                                                   2.5e-05 
                                                                   derivativek_169)
                                                                
                                                                derivativek_169))
                                                  
                                                  (( *. ) (( *. ) 0.1584 
                                                                  errork_179)
                                                           integralk_184)) 
                                            (( *. ) (( *. ) 0.0008 
                                                            errork_179) 
                                                    derivativek_169)) 
                                      (( *. ) (( *. ) 0.0099  integralk_184) 
                                              derivativek_169) in
                             let ((errork1help2_182:float): float) =
                                 (-.) ((+.) ((-.) ((+.) ((+.) (( *. ) 
                                                                 (( *. ) 
                                                                    0.64 
                                                                    errork_179)
                                                                  errork_179)
                                                              
                                                              (( *. ) 
                                                                 (( *. ) 
                                                                    0.01 
                                                                    integralk_184)
                                                                 
                                                                 integralk_184))
                                                        
                                                        (( *. ) (( *. ) 
                                                                   0.0025 
                                                                   derivativek_169)
                                                                
                                                                derivativek_169))
                                                  
                                                  (( *. ) (( *. ) 0.16 
                                                                  errork_179)
                                                           integralk_184)) 
                                            (( *. ) (( *. ) 0.08  errork_179)
                                                     derivativek_169)) 
                                      (( *. ) (( *. ) 0.01  integralk_184) 
                                              derivativek_169) in
                             let ((energyk1v2_177:float): float) =
                                 self.energyk1_176 in
                             let ((derivativek1help_171:float): float) =
                                 (+.) ((-.) (( *. ) (-2.)  errork_179) 
                                            integralk_184) 
                                      (( *. ) 0.5  derivativek_169) in
                             let ((integralk1help_186:float): float) =
                                 (+.) ((+.) (( *. ) 0.08  errork_179) 
                                            (( *. ) 0.99  integralk_184)) 
                                      (( *. ) 0.005  derivativek_169) in
                             let ((errork1help_181:float): float) =
                                 (+.) ((-.) (( *. ) 0.8  errork_179) 
                                            (( *. ) 0.1  integralk_184)) 
                                      (( *. ) 0.05  derivativek_169) in
                             let ((diffenergy1_173:float): float) =
                                 (-.) ((+.) ((+.) ((+.) (( *. ) (( *. ) 
                                                                   1.1375 
                                                                   self.errork1_180)
                                                                
                                                                self.errork1_180)
                                                        
                                                        (( *. ) (( *. ) 
                                                                   1.25 
                                                                   self.integralk1_185)
                                                                
                                                                self.integralk1_185))
                                                  
                                                  (( *. ) (( *. ) 0.05 
                                                                  self.derivativek1_170)
                                                          
                                                          self.derivativek1_170))
                                            
                                            (( *. ) (( *. ) 1. 
                                                            self.errork1_180)
                                                     self.integralk1_185)) 
                                      ((+.) ((+.) ((+.) (( *. ) (( *. ) 
                                                                   1.1375 
                                                                   errork_179)
                                                                 errork_179) 
                                                        (( *. ) (( *. ) 
                                                                   1.25 
                                                                   integralk_184)
                                                                
                                                                integralk_184))
                                                  
                                                  (( *. ) (( *. ) 0.05 
                                                                  derivativek_169)
                                                           derivativek_169)) 
                                            (( *. ) (( *. ) 1.  errork_179) 
                                                    integralk_184)) in
                             let ((energykv2_178:float): float) = energyk_175 in
                             let (derivativek_164:float) = derivativek_169 in
                             let (integralk_166:float) = integralk_184 in
                             let (errork_165:float) = errork_179 in
                             let (uk_167:float) = uk_188 in
                             let (xk_168:float) = xk_189 in
                             let _ = print_float xk_168 in
                             let _ = print_string "," in
                             let _ = print_float uk_167 in
                             let _ = print_string "," in
                             let _ = print_float errork_165 in
                             let _ = print_string "," in
                             let _ = print_float integralk_166 in
                             let _ = print_string "," in
                             let _ = print_float derivativek_164 in
                             self.result_158 <- print_newline ())))))
                    | _ -> self.result_158 <- ()  end) ; self.result_158)) in
       cstate_206.horizon <- min cstate_206.horizon  self.h_163 ; result_211)):
    unit) in 
  let main_reset self  =
    ((self.i_161 <- true ;
      self.derivativek1_170 <- 0. ;
      self.integralk1_185 <- 0. ;
      self.errork1_180 <- 1. ;
      self.xk1_190 <- 0. ; self.energyk1_176 <- 1.1375):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
