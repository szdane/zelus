(* The Zelus compiler, version 2.2-dev
  (2026-10-16-14:37) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let kd = 0.5

let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable xk1_158 : 'e ;
    mutable integralk1_154 : 'd ;
    mutable errork1_151 : 'c ;
    mutable energyk1bound_141 : 'b ; mutable derivativek1_137 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_158 = (42.:float) ;
      integralk1_154 = (42.:float) ;
      errork1_151 = (42.:float) ;
      energyk1bound_141 = (42.:float) ; derivativek1_137 = (42.:float) } in
  let exec_reset self  =
    ((self.derivativek1_137 <- 0. ;
      self.integralk1_154 <- 0. ;
      self.errork1_151 <- 1. ;
      self.xk1_158 <- 0. ; self.energyk1bound_141 <- 1.1375):unit) in 
  let exec_step self () =
    ((let (l_160:float) = self.derivativek1_137 in
      let ((derivativek_136:float): float) = l_160 in
      let (l_163:float) = self.integralk1_154 in
      let ((integralk_153:float): float) = l_163 in
      let (l_162:float) = self.errork1_151 in
      let ((errork_150:float): float) = l_162 in
      let ((uk_156:float): float) =
          (-.) ((+.) (( *. ) kp  errork_150)  (( *. ) ki  integralk_153)) 
               (( *. ) kd  derivativek_136) in
      let (l_164:float) = self.xk1_158 in
      let ((xk_157:float): float) = l_164 in
      let ((copy_212:float): float) = (+.) xk_157  (( *. ) uk_156  dt) in
      self.xk1_158 <- copy_212 ;
      (let ((copy_211:float): float) = (-.) r  self.xk1_158 in
       self.errork1_151 <- copy_211 ;
       (let ((copy_210:float): float) =
            (+.) integralk_153  (( *. ) self.errork1_151  dt) in
        self.integralk1_154 <- copy_210 ;
        (let ((copy_209:float): float) =
             (/.) ((-.) self.errork1_151  errork_150)  dt in
         self.derivativek1_137 <- copy_209 ;
         (let ((energyk1_140:float): float) =
              (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375  self.errork1_151) 
                                       self.errork1_151) 
                               (( *. ) (( *. ) 1.25  self.integralk1_154) 
                                       self.integralk1_154)) 
                         (( *. ) (( *. ) 0.05  self.derivativek1_137) 
                                 self.derivativek1_137)) 
                   (( *. ) self.errork1_151  self.integralk1_154) in
          let ((copy_208:float): float) = energyk1_140 in
          let (l_161:float) = self.energyk1bound_141 in
          self.energyk1bound_141 <- copy_208 ;
          (let ((xkbound_159:float): float) = xk_157 in
           let ((derivativek1dev_138:float): float) =
               (+.) ((-.) (( *. ) (-2.)  errork_150)  integralk_153) 
                    (( *. ) 0.5  derivativek_136) in
           let ((energyk1p3_146:float): float) =
               ( *. ) (( *. ) 0.05  derivativek1dev_138)  derivativek1dev_138 in
           let ((energyk1p3dev_147:float): float) = energyk1p3_146 in
           let ((integralk1dev_155:float): float) =
               (+.) ((+.) (( *. ) 0.08  errork_150) 
                          (( *. ) 0.99  integralk_153)) 
                    (( *. ) 0.005  derivativek_136) in
           let ((energyk1p2_144:float): float) =
               ( *. ) (( *. ) 1.25  integralk1dev_155)  integralk1dev_155 in
           let ((energyk1p2dev_145:float): float) = energyk1p2_144 in
           let ((errork1dev_152:float): float) =
               (+.) ((-.) (( *. ) 0.8  errork_150) 
                          (( *. ) 0.1  integralk_153)) 
                    (( *. ) 0.05  derivativek_136) in
           let ((energyk1p1_142:float): float) =
               ( *. ) (( *. ) 1.1375  errork1dev_152)  errork1dev_152 in
           let ((energyk1p1dev_143:float): float) = energyk1p1_142 in
           let ((energyk1p4_148:float): float) =
               ( *. ) errork1dev_152  integralk1dev_155 in
           let ((energyk1p4dev_149:float): float) = energyk1p4_148 in
           let ((energyk_139:float): float) = l_161 in
           (xk_157 , uk_156 , errork_150 , integralk_153 , derivativek_136))))))):
    float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_166 : 'j ;
    mutable h_173 : 'i ;
    mutable i_171 : 'h ;
    mutable h_169 : 'g ;
    mutable result_168 : 'f ;
    mutable xk1_201 : 'e ;
    mutable integralk1_197 : 'd ;
    mutable errork1_194 : 'c ;
    mutable energyk1bound_184 : 'b ; mutable derivativek1_180 : 'a }

let main (cstate_218:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_166 = false ;
      h_173 = 42. ;
      i_171 = (false:bool) ;
      h_169 = (42.:float) ;
      result_168 = (():unit) ;
      xk1_201 = (42.:float) ;
      integralk1_197 = (42.:float) ;
      errork1_194 = (42.:float) ;
      energyk1bound_184 = (42.:float) ; derivativek1_180 = (42.:float) } in
  let main_step self ((time_165:float) , ()) =
    ((self.major_166 <- cstate_218.major ;
      (let (result_223:unit) =
           let h_172 = ref (infinity:float) in
           (if self.i_171 then self.h_169 <- (+.) time_165  0.) ;
           (let (z_170:bool) =
                (&&) self.major_166  ((>=) time_165  self.h_169) in
            self.h_169 <- (if z_170 then (+.) self.h_169  0.1 else self.h_169)
            ;
            h_172 := min !h_172  self.h_169 ;
            self.h_173 <- !h_172 ;
            self.i_171 <- false ;
            (let (trigger_167:zero) = z_170 in
             (begin match trigger_167 with
                    | true ->
                        let () = () in
                        let (l_203:float) = self.derivativek1_180 in
                        let ((derivativek_179:float): float) = l_203 in
                        let (l_206:float) = self.integralk1_197 in
                        let ((integralk_196:float): float) = l_206 in
                        let (l_205:float) = self.errork1_194 in
                        let ((errork_193:float): float) = l_205 in
                        let ((uk_199:float): float) =
                            (-.) ((+.) (( *. ) kp  errork_193) 
                                       (( *. ) ki  integralk_196)) 
                                 (( *. ) kd  derivativek_179) in
                        let (l_207:float) = self.xk1_201 in
                        let ((xk_200:float): float) = l_207 in
                        let ((copy_217:float): float) =
                            (+.) xk_200  (( *. ) uk_199  dt) in
                        self.xk1_201 <- copy_217 ;
                        (let ((copy_216:float): float) = (-.) r  self.xk1_201 in
                         self.errork1_194 <- copy_216 ;
                         (let ((copy_215:float): float) =
                              (+.) integralk_196 
                                   (( *. ) self.errork1_194  dt) in
                          self.integralk1_197 <- copy_215 ;
                          (let ((copy_214:float): float) =
                               (/.) ((-.) self.errork1_194  errork_193)  dt in
                           self.derivativek1_180 <- copy_214 ;
                           (let ((energyk1_183:float): float) =
                                (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375 
                                                                 self.errork1_194)
                                                          self.errork1_194) 
                                                 (( *. ) (( *. ) 1.25 
                                                                 self.integralk1_197)
                                                          self.integralk1_197))
                                           
                                           (( *. ) (( *. ) 0.05 
                                                           self.derivativek1_180)
                                                    self.derivativek1_180)) 
                                     (( *. ) self.errork1_194 
                                             self.integralk1_197) in
                            let ((copy_213:float): float) = energyk1_183 in
                            let (l_204:float) = self.energyk1bound_184 in
                            self.energyk1bound_184 <- copy_213 ;
                            (let ((xkbound_202:float): float) = xk_200 in
                             let ((derivativek1dev_181:float): float) =
                                 (+.) ((-.) (( *. ) (-2.)  errork_193) 
                                            integralk_196) 
                                      (( *. ) 0.5  derivativek_179) in
                             let ((energyk1p3_189:float): float) =
                                 ( *. ) (( *. ) 0.05  derivativek1dev_181) 
                                        derivativek1dev_181 in
                             let ((energyk1p3dev_190:float): float) =
                                 energyk1p3_189 in
                             let ((integralk1dev_198:float): float) =
                                 (+.) ((+.) (( *. ) 0.08  errork_193) 
                                            (( *. ) 0.99  integralk_196)) 
                                      (( *. ) 0.005  derivativek_179) in
                             let ((energyk1p2_187:float): float) =
                                 ( *. ) (( *. ) 1.25  integralk1dev_198) 
                                        integralk1dev_198 in
                             let ((energyk1p2dev_188:float): float) =
                                 energyk1p2_187 in
                             let ((errork1dev_195:float): float) =
                                 (+.) ((-.) (( *. ) 0.8  errork_193) 
                                            (( *. ) 0.1  integralk_196)) 
                                      (( *. ) 0.05  derivativek_179) in
                             let ((energyk1p1_185:float): float) =
                                 ( *. ) (( *. ) 1.1375  errork1dev_195) 
                                        errork1dev_195 in
                             let ((energyk1p1dev_186:float): float) =
                                 energyk1p1_185 in
                             let ((energyk1p4_191:float): float) =
                                 ( *. ) errork1dev_195  integralk1dev_198 in
                             let ((energyk1p4dev_192:float): float) =
                                 energyk1p4_191 in
                             let ((energyk_182:float): float) = l_204 in
                             let (derivativek_174:float) = derivativek_179 in
                             let (integralk_176:float) = integralk_196 in
                             let (errork_175:float) = errork_193 in
                             let (uk_177:float) = uk_199 in
                             let (xk_178:float) = xk_200 in
                             let _ = print_float xk_178 in
                             let _ = print_string "," in
                             let _ = print_float uk_177 in
                             let _ = print_string "," in
                             let _ = print_float errork_175 in
                             let _ = print_string "," in
                             let _ = print_float integralk_176 in
                             let _ = print_string "," in
                             let _ = print_float derivativek_174 in
                             self.result_168 <- print_newline ())))))
                    | _ -> self.result_168 <- ()  end) ; self.result_168)) in
       cstate_218.horizon <- min cstate_218.horizon  self.h_173 ; result_223)):
    unit) in 
  let main_reset self  =
    ((self.i_171 <- true ;
      self.derivativek1_180 <- 0. ;
      self.integralk1_197 <- 0. ;
      self.errork1_194 <- 1. ;
      self.xk1_201 <- 0. ; self.energyk1bound_184 <- 1.1375):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
