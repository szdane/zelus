(* The Zelus compiler, version 2.2-dev
  (2026-11-4-20:25) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = (/.) (( *. ) 0.2  1.)  dt

let kd = ( *. ) 0.625  ((-.) 1.  (( *. ) kp  dt))

let calc_energyk1v2 (((energyk1_199:float): float) ,
                     ((alpha_194:float): float) ,
                     ((beta_195:float): float) ,
                     ((errork1dev_202:float): float) ,
                     ((derivativek1dev_198:float): float) ,
                     ((errork1_201:float): float) ,
                     ((derivativek1_197:float): float) ,
                     ((errork_200:float): float) ,
                     ((derivativek_196:float): float)) =
  let ((energyk1v2_203:float): float) = energyk1_199 in
  energyk1v2_203

let calc_energyk1vf (((energyk1v2_208:float): float) ,
                     ((alpha_204:float): float) ,
                     ((beta_205:float): float) ,
                     ((errork1dev_210:float): float) ,
                     ((derivativek1dev_207:float): float) ,
                     ((errork_209:float): float) ,
                     ((derivativek_206:float): float)) =
  let ((energyk1vf_211:float): float) = energyk1v2_208 in
  energyk1vf_211

let calc_diffenergy (((energyk1vf_215:float): float) ,
                     ((energykv2_216:float): float) ,
                     ((energyk1_214:float): float) ,
                     ((energyk_213:float): float) ,
                     ((errork_217:float): float) ,
                     ((derivativek_212:float): float)) =
  let ((diffenergyv1_218:float): float) = (-.) energyk1vf_215  energykv2_216 in
  let ((diffenergyv2_219:float): float) = diffenergyv1_218 in
  let ((diffenergyvf_220:float): float) = diffenergyv2_219 in
  diffenergyvf_220

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_244 : 'e ;
    mutable xk1_238 : 'd ;
    mutable errork1_234 : 'c ;
    mutable energyk1bound_229 : 'b ; mutable derivativek1_224 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_244 = (false:bool) ;
      xk1_238 = (42.:float) ;
      errork1_234 = (42.:float) ;
      energyk1bound_229 = (42.:float) ; derivativek1_224 = (42.:float) } in
  let exec_reset self  =
    ((self.derivativek1_224 <- 0. ; self.i_244 <- true ; self.xk1_238 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_240:float) = self.derivativek1_224 in
      let ((derivativek_223:float): float) = l_240 in
      (if self.i_244 then self.errork1_234 <- r) ;
      (let (l_242:float) = self.errork1_234 in
       let ((errork_233:float): float) = l_242 in
       let ((uk_236:float): float) =
           (-.) (( *. ) kp  errork_233)  (( *. ) kd  derivativek_223) in
       let (l_243:float) = self.xk1_238 in
       let ((xk_237:float): float) = l_243 in
       let ((copy_285:float): float) = (+.) xk_237  (( *. ) uk_236  dt) in
       self.xk1_238 <- copy_285 ;
       (let ((copy_284:float): float) = (-.) r  self.xk1_238 in
        self.errork1_234 <- copy_284 ;
        (let ((copy_283:float): float) =
             (/.) ((-.) self.errork1_234  errork_233)  dt in
         self.derivativek1_224 <- copy_283 ;
         (let ((beta_222:float): float) =
              ( *. ) ((-.) 1.  (( *. ) kp  dt))  dt in
          let ((alpha_221:float): float) = kp in
          let ((energyk1_228:float): float) =
              (+.) (( *. ) (( *. ) alpha_221  self.errork1_234) 
                           self.errork1_234) 
                   (( *. ) (( *. ) beta_222  self.derivativek1_224) 
                           self.derivativek1_224) in
          let ((copy_282:float): float) = energyk1_228 in
          (if self.i_244 then self.energyk1bound_229 <- alpha_221) ;
          (let (l_241:float) = self.energyk1bound_229 in
           self.energyk1bound_229 <- copy_282 ;
           self.i_244 <- false ;
           (let ((xkbound_239:float): float) = xk_237 in
            let ((energyk_227:float): float) = l_241 in
            let ((energykv2_232:float): float) = energyk_227 in
            let ((derivativek1dev_225:float): float) =
                (+.) ((-.) 0.  (( *. ) kp  errork_233)) 
                     (( *. ) kd  derivativek_223) in
            let ((errork1dev_235:float): float) =
                (+.) (( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_233) 
                     (( *. ) (( *. ) kd  dt)  derivativek_223) in
            let ((energyk1v2_230:float): float) =
                calc_energyk1v2 (energyk1_228 ,
                                 alpha_221 ,
                                 beta_222 ,
                                 errork1dev_235 ,
                                 derivativek1dev_225 ,
                                 self.errork1_234 ,
                                 self.derivativek1_224 ,
                                 errork_233 , derivativek_223) in
            let ((energyk1vf_231:float): float) =
                calc_energyk1vf (energyk1v2_230 ,
                                 alpha_221 ,
                                 beta_222 ,
                                 errork1dev_235 ,
                                 derivativek1dev_225 ,
                                 errork_233 , derivativek_223) in
            let ((diffenergy_226:float): float) =
                calc_diffenergy (energyk1vf_231 ,
                                 energykv2_232 ,
                                 energyk1_228 ,
                                 energyk_227 , errork_233 , derivativek_223) in
            (xk_237 , uk_236 , errork_233 , derivativek_223)))))))):float *
                                                                    float *
                                                                    float *
                                                                    float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_246 : 'j ;
    mutable h_253 : 'i ;
    mutable i_251 : 'h ;
    mutable h_249 : 'g ;
    mutable result_248 : 'f ;
    mutable i_281 : 'e ;
    mutable xk1_275 : 'd ;
    mutable errork1_271 : 'c ;
    mutable energyk1bound_266 : 'b ; mutable derivativek1_261 : 'a }

let main (cstate_290:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_246 = false ;
      h_253 = 42. ;
      i_251 = (false:bool) ;
      h_249 = (42.:float) ;
      result_248 = (():unit) ;
      i_281 = (false:bool) ;
      xk1_275 = (42.:float) ;
      errork1_271 = (42.:float) ;
      energyk1bound_266 = (42.:float) ; derivativek1_261 = (42.:float) } in
  let main_step self ((time_245:float) , ()) =
    ((self.major_246 <- cstate_290.major ;
      (let (result_295:unit) =
           let h_252 = ref (infinity:float) in
           (if self.i_251 then self.h_249 <- (+.) time_245  0.) ;
           (let (z_250:bool) =
                (&&) self.major_246  ((>=) time_245  self.h_249) in
            self.h_249 <- (if z_250 then (+.) self.h_249  0.1 else self.h_249)
            ;
            h_252 := min !h_252  self.h_249 ;
            self.h_253 <- !h_252 ;
            self.i_251 <- false ;
            (let (trigger_247:zero) = z_250 in
             (begin match trigger_247 with
                    | true ->
                        let ((alpha_258:float): float) = kp in
                        (if self.i_281 then
                         self.energyk1bound_266 <- alpha_258) ;
                        (if self.i_281 then self.errork1_271 <- r) ;
                        self.i_281 <- false ;
                        (let () = () in
                         let (l_277:float) = self.derivativek1_261 in
                         let ((derivativek_260:float): float) = l_277 in
                         let (l_279:float) = self.errork1_271 in
                         let ((errork_270:float): float) = l_279 in
                         let ((uk_273:float): float) =
                             (-.) (( *. ) kp  errork_270) 
                                  (( *. ) kd  derivativek_260) in
                         let (l_280:float) = self.xk1_275 in
                         let ((xk_274:float): float) = l_280 in
                         let ((copy_289:float): float) =
                             (+.) xk_274  (( *. ) uk_273  dt) in
                         self.xk1_275 <- copy_289 ;
                         (let ((copy_288:float): float) =
                              (-.) r  self.xk1_275 in
                          self.errork1_271 <- copy_288 ;
                          (let ((copy_287:float): float) =
                               (/.) ((-.) self.errork1_271  errork_270)  dt in
                           self.derivativek1_261 <- copy_287 ;
                           (let ((beta_259:float): float) =
                                ( *. ) ((-.) 1.  (( *. ) kp  dt))  dt in
                            let ((energyk1_265:float): float) =
                                (+.) (( *. ) (( *. ) alpha_258 
                                                     self.errork1_271) 
                                             self.errork1_271) 
                                     (( *. ) (( *. ) beta_259 
                                                     self.derivativek1_261) 
                                             self.derivativek1_261) in
                            let ((copy_286:float): float) = energyk1_265 in
                            let (l_278:float) = self.energyk1bound_266 in
                            self.energyk1bound_266 <- copy_286 ;
                            (let ((xkbound_276:float): float) = xk_274 in
                             let ((energyk_264:float): float) = l_278 in
                             let ((energykv2_269:float): float) = energyk_264 in
                             let ((derivativek1dev_262:float): float) =
                                 (+.) ((-.) 0.  (( *. ) kp  errork_270)) 
                                      (( *. ) kd  derivativek_260) in
                             let ((errork1dev_272:float): float) =
                                 (+.) (( *. ) ((-.) 1.  (( *. ) kp  dt)) 
                                              errork_270) 
                                      (( *. ) (( *. ) kd  dt) 
                                              derivativek_260) in
                             let ((energyk1v2_267:float): float) =
                                 calc_energyk1v2 (energyk1_265 ,
                                                  alpha_258 ,
                                                  beta_259 ,
                                                  errork1dev_272 ,
                                                  derivativek1dev_262 ,
                                                  self.errork1_271 ,
                                                  self.derivativek1_261 ,
                                                  errork_270 ,
                                                  derivativek_260) in
                             let ((energyk1vf_268:float): float) =
                                 calc_energyk1vf (energyk1v2_267 ,
                                                  alpha_258 ,
                                                  beta_259 ,
                                                  errork1dev_272 ,
                                                  derivativek1dev_262 ,
                                                  errork_270 ,
                                                  derivativek_260) in
                             let ((diffenergy_263:float): float) =
                                 calc_diffenergy (energyk1vf_268 ,
                                                  energykv2_269 ,
                                                  energyk1_265 ,
                                                  energyk_264 ,
                                                  errork_270 ,
                                                  derivativek_260) in
                             let (derivativek_254:float) = derivativek_260 in
                             let (errork_255:float) = errork_270 in
                             let (uk_256:float) = uk_273 in
                             let (xk_257:float) = xk_274 in
                             let _ = print_float xk_257 in
                             let _ = print_string "," in
                             let _ = print_float uk_256 in
                             let _ = print_string "," in
                             let _ = print_float errork_255 in
                             let _ = print_string "," in
                             let _ = print_float derivativek_254 in
                             self.result_248 <- print_newline ())))))
                    | _ -> self.result_248 <- ()  end) ; self.result_248)) in
       cstate_290.horizon <- min cstate_290.horizon  self.h_253 ; result_295)):
    unit) in 
  let main_reset self  =
    ((self.i_251 <- true ;
      self.i_281 <- true ; self.derivativek1_261 <- 0. ; self.xk1_275 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
