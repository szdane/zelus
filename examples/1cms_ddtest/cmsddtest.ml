(* The Zelus compiler, version 2.2-dev
  (2026-08-12-13:42) *)
open Ztypes
let setpoint = 1.

let sysuncertainty = 1.1

let m = ( *. ) 4.  sysuncertainty

let k = ( *. ) 15.  sysuncertainty

let b = ( *. ) 4.  sysuncertainty

let piduncertainty = 1.

let kp = ( *. ) 80.  piduncertainty

let ki = ( *. ) 20.  piduncertainty

let kd = ( *. ) 25.  piduncertainty

let dt = 0.1

let u_max = 40.

let u_min = (-40.)

let a1 = (-.) ((/.) (( *. ) ((+.) b  kd)  dt)  m)  3.

let a2 = (+.) 3. 
              ((/.) ((+.) (( *. ) (( *. ) (-2.)  ((+.) b  kd))  dt) 
                          (( *. ) (( *. ) ((+.) kp  k)  dt)  dt))  m)

let a3 = (-.) ((/.) ((+.) ((-.) (( *. ) ((+.) b  kd)  dt) 
                                (( *. ) (( *. ) ((+.) kp  k)  dt)  dt)) 
                          (( *. ) (( *. ) (( *. ) ki  dt)  dt)  dt))  
                    m)  1.

let stability_condition1 = a3

let stability_condition2 = (+.) ((+.) ((+.) 1.  a1)  a2)  a3

let stability_condition3 = (+.) ((-.) ((+.) (-1.)  a1)  a2)  a3

let stability_condition41 = (-.) ((+.) ((-.) 1.  (( *. ) a3  a3)) 
                                       (( *. ) a1  a3))  a2

let stability_condition42 = (+.) ((-.) ((-.) 1.  (( *. ) a3  a3)) 
                                       (( *. ) a1  a3))  a2

type _saturate_umax = unit

let saturate_umax  = 
   let saturate_umax_alloc _ = () in
  let saturate_umax_reset self  =
    ((()):unit) in 
  let saturate_umax_step self ((u_217:float): float) =
    (((if (>) u_217  u_max then u_max else u_217)):float) in
  Node { alloc = saturate_umax_alloc; reset = saturate_umax_reset ;
                                      step = saturate_umax_step }
type ('b , 'a) _saturate_u_cont_sym =
  { mutable i_329 : 'b ; mutable i_328 : 'a }

let saturate_u_cont_sym  = 
  let Node { alloc = i_329_alloc; step = i_329_step ; reset = i_329_reset } = saturate_umax 
   in 
  let Node { alloc = i_328_alloc; step = i_328_step ; reset = i_328_reset } = saturate_umax 
   in
  let saturate_u_cont_sym_alloc _ =
    ();
    { i_329 = i_329_alloc () (* discrete *)  ;
      i_328 = i_328_alloc () (* discrete *)  } in
  let saturate_u_cont_sym_reset self  =
    ((i_329_reset self.i_329  ; i_328_reset self.i_328 ):unit) in 
  let saturate_u_cont_sym_step self ((u_218:float): float) =
    ((let (next_219:float) = i_329_step self.i_329 u_218 in
      if (<) (i_328_step self.i_328 u_218)  u_min then u_min else next_219):
    float) in
  Node { alloc = saturate_u_cont_sym_alloc; reset = saturate_u_cont_sym_reset
                                            ; step = saturate_u_cont_sym_step }
type ('a) _noise =
  { mutable theta_221 : 'a }

let noise  = 
   let noise_alloc _ =
     ();{ theta_221 = (42.:float) } in
  let noise_reset self  =
    (self.theta_221 <- 0.:unit) in 
  let noise_step self () =
    ((let (l_222:float) = self.theta_221 in
      self.theta_221 <- (+.) l_222  (( *. ) 5.  dt) ;
      (let ((n_220:float): float) = ( *. ) 0.05  (cos self.theta_221) in
       n_220)):float) in
  Node { alloc = noise_alloc; reset = noise_reset ; step = noise_step }
type ('b , 'a) _sys =
  { mutable x_225 : 'b ; mutable v_224 : 'a }

let sys  = 
   let sys_alloc _ =
     ();{ x_225 = (42.:float) ; v_224 = (42.:float) } in
  let sys_reset self  =
    ((self.x_225 <- 0. ; self.v_224 <- 0.):unit) in 
  let sys_step self ((u_223:float): float) =
    ((let (l_226:float) = self.v_224 in
      let (l_227:float) = self.x_225 in
      let ((copy_313:float): float) = (+.) l_227  (( *. ) l_226  dt) in
      self.x_225 <- copy_313 ;
      (let ((copy_312:float): float) =
           (+.) l_226 
                ((/.) (( *. ) ((+.) ((-.) (( *. ) ((~-.) k)  l_227) 
                                          (( *. ) b  l_226))  u_223)  
                              dt)  m) in
       self.v_224 <- copy_312 ; (self.x_225 , self.v_224))):float * float) in
  Node { alloc = sys_alloc; reset = sys_reset ; step = sys_step }
type ('a) _pid =
  { mutable integral_antiwindup_231 : 'a }

let pid  = 
   let pid_alloc _ =
     ();{ integral_antiwindup_231 = (42.:float) } in
  let pid_reset self  =
    (self.integral_antiwindup_231 <- 0.:unit) in 
  let pid_step self (((x_229:float): float) , ((v_228:float): float)) =
    ((let ((error_230:float): float) = (-.) setpoint  x_229 in
      let (l_234:float) = self.integral_antiwindup_231 in
      let ((copy_314:float): float) = (+.) l_234  (( *. ) dt  error_230) in
      self.integral_antiwindup_231 <- copy_314 ;
      (let ((u_232:float): float) =
           (-.) ((+.) (( *. ) kp  error_230)  (( *. ) ki  l_234)) 
                (( *. ) kd  v_228) in
       let ((u_sat_233:float): float) = u_232 in
       (error_230 , u_sat_233))):float * float) in
  Node { alloc = pid_alloc; reset = pid_reset ; step = pid_step }
type ('b , 'a) _pid_esin =
  { mutable i_330 : 'b ; mutable integral_antiwindup_239 : 'a }

let pid_esin  = 
  let Node { alloc = i_330_alloc; step = i_330_step ; reset = i_330_reset } = saturate_u_cont_sym 
   in
  let pid_esin_alloc _ =
    ();
    { integral_antiwindup_239 = (42.:float);
      i_330 = i_330_alloc () (* discrete *)  } in
  let pid_esin_reset self  =
    ((self.integral_antiwindup_239 <- 0. ; i_330_reset self.i_330 ):unit) in 
  let pid_esin_step self (((x_237:float): float) ,
                          ((v_236:float): float) , ((noise_235:float): float)) =
    ((let ((error_238:float): float) = (-.) setpoint  ((+.) x_237  noise_235) in
      let (l_242:float) = self.integral_antiwindup_239 in
      let ((u_240:float): float) =
          (-.) ((+.) (( *. ) kp  error_238)  (( *. ) ki  l_242)) 
               (( *. ) kd  ((+.) v_236  0.)) in
      let ((copy_315:float): float) =
          if (||) ((&&) ((>) u_240  u_max)  ((>) error_238  0.)) 
                  ((&&) ((<) u_240  u_min)  ((<) error_238  0.))
          then l_242
          else (+.) l_242  (( *. ) dt  error_238) in
      self.integral_antiwindup_239 <- copy_315 ;
      (let ((u_sat_241:float): float) = i_330_step self.i_330 u_240 in
       (error_238 , u_sat_241))):float * float) in
  Node { alloc = pid_esin_alloc; reset = pid_esin_reset ;
                                 step = pid_esin_step }
type ('b , 'a) _pid_estat =
  { mutable i_331 : 'b ; mutable integral_antiwindup_246 : 'a }

let pid_estat  = 
  let Node { alloc = i_331_alloc; step = i_331_step ; reset = i_331_reset } = saturate_u_cont_sym 
   in
  let pid_estat_alloc _ =
    ();
    { integral_antiwindup_246 = (42.:float);
      i_331 = i_331_alloc () (* discrete *)  } in
  let pid_estat_reset self  =
    ((self.integral_antiwindup_246 <- 0. ; i_331_reset self.i_331 ):unit) in 
  let pid_estat_step self (((x_244:float): float) , ((v_243:float): float)) =
    ((let ((error_245:float): float) = (-.) setpoint  ((-.) x_244  0.5) in
      let (l_249:float) = self.integral_antiwindup_246 in
      let ((u_247:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_245)  (( *. ) ki  l_249)) 
                     (( *. ) kd  ((+.) v_243  0.)))  0. in
      let ((copy_316:float): float) =
          if (||) ((&&) ((>) u_247  u_max)  ((>) error_245  0.)) 
                  ((&&) ((<) u_247  u_min)  ((<) error_245  0.))
          then l_249
          else (+.) l_249  (( *. ) dt  error_245) in
      self.integral_antiwindup_246 <- copy_316 ;
      (let ((u_sat_248:float): float) = i_331_step self.i_331 u_247 in
       (error_245 , u_sat_248))):float * float) in
  Node { alloc = pid_estat_alloc; reset = pid_estat_reset ;
                                  step = pid_estat_step }
type ('b , 'a) _pid_e =
  { mutable i_332 : 'b ; mutable integral_antiwindup_254 : 'a }

let pid_e  = 
  let Node { alloc = i_332_alloc; step = i_332_step ; reset = i_332_reset } = saturate_u_cont_sym 
   in
  let pid_e_alloc _ =
    ();
    { integral_antiwindup_254 = (42.:float);
      i_332 = i_332_alloc () (* discrete *)  } in
  let pid_e_reset self  =
    ((self.integral_antiwindup_254 <- 0. ; i_332_reset self.i_332 ):unit) in 
  let pid_e_step self (((x_252:float): float) ,
                       ((v_251:float): float) , ((noise_250:float): float)) =
    ((let ((error_253:float): float) =
          (-.) setpoint  ((-.) ((+.) x_252  noise_250)  0.5) in
      let (l_257:float) = self.integral_antiwindup_254 in
      let ((u_255:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_253)  (( *. ) ki  l_257)) 
                     (( *. ) kd  ((+.) v_251  0.)))  noise_250 in
      let ((copy_317:float): float) =
          if (||) ((&&) ((>) u_255  u_max)  ((>) error_253  0.)) 
                  ((&&) ((<) u_255  u_min)  ((<) error_253  0.))
          then l_257
          else (+.) l_257  (( *. ) dt  error_253) in
      self.integral_antiwindup_254 <- copy_317 ;
      (let ((u_sat_256:float): float) = i_332_step self.i_332 u_255 in
       (error_253 , u_sat_256))):float * float) in
  Node { alloc = pid_e_alloc; reset = pid_e_reset ; step = pid_e_step }
type ('d , 'c , 'b , 'a) _exec =
  { mutable i_334 : 'd ;
    mutable i_333 : 'c ; mutable x_261 : 'b ; mutable v_260 : 'a }

let exec  = 
  let Node { alloc = i_334_alloc; step = i_334_step ; reset = i_334_reset } = pid 
   in 
  let Node { alloc = i_333_alloc; step = i_333_step ; reset = i_333_reset } = sys 
   in
  let exec_alloc _ =
    ();
    { x_261 = (42.:float) ; v_260 = (42.:float);
      i_334 = i_334_alloc () (* discrete *)  ;
      i_333 = i_333_alloc () (* discrete *)  } in
  let exec_reset self  =
    ((self.v_260 <- 0. ;
      self.x_261 <- 0. ; i_334_reset self.i_334  ; i_333_reset self.i_333 ):
    unit) in 
  let exec_step self () =
    ((let (l_262:float) = self.v_260 in
      let (l_263:float) = self.x_261 in
      let ((error_258:float) , (u_259:float)) =
          i_334_step self.i_334 (l_263 , l_262) in
      let ((copy_318:float) , (copy_319:float)) = i_333_step self.i_333 u_259 in
      self.x_261 <- copy_318 ;
      self.v_260 <- copy_319 ; (self.x_261 , self.v_260 , error_258 , u_259)):
    float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('e , 'd , 'c , 'b , 'a) _exec_esin =
  { mutable i_336 : 'e ;
    mutable i_335 : 'd ;
    mutable theta_270 : 'c ; mutable x_268 : 'b ; mutable v_267 : 'a }

let exec_esin  = 
  let Node { alloc = i_336_alloc; step = i_336_step ; reset = i_336_reset } = pid_esin 
   in 
  let Node { alloc = i_335_alloc; step = i_335_step ; reset = i_335_reset } = sys 
   in
  let exec_esin_alloc _ =
    ();
    { theta_270 = (42.:float) ; x_268 = (42.:float) ; v_267 = (42.:float);
      i_336 = i_336_alloc () (* discrete *)  ;
      i_335 = i_335_alloc () (* discrete *)  } in
  let exec_esin_reset self  =
    ((self.theta_270 <- 0. ;
      self.v_267 <- 0. ;
      self.x_268 <- 0. ; i_336_reset self.i_336  ; i_335_reset self.i_335 ):
    unit) in 
  let exec_esin_step self () =
    ((let (l_273:float) = self.theta_270 in
      self.theta_270 <- (+.) l_273  (( *. ) 5.  dt) ;
      (let ((n_269:float): float) = ( *. ) 0.05  (cos self.theta_270) in
       let (n_265:float) = n_269 in
       let (l_271:float) = self.v_267 in
       let (l_272:float) = self.x_268 in
       let ((error_264:float) , (u_266:float)) =
           i_336_step self.i_336 (l_272 , l_271 , n_265) in
       let ((copy_320:float) , (copy_321:float)) =
           i_335_step self.i_335 u_266 in
       self.x_268 <- copy_320 ;
       self.v_267 <- copy_321 ;
       (let () = () in
        (self.x_268 , self.v_267 , error_264 , u_266 , n_265)))):float *
                                                                 float *
                                                                 float *
                                                                 float *
                                                                 float) in
  Node { alloc = exec_esin_alloc; reset = exec_esin_reset ;
                                  step = exec_esin_step }
type ('d , 'c , 'b , 'a) _exec_estat =
  { mutable i_338 : 'd ;
    mutable i_337 : 'c ; mutable x_277 : 'b ; mutable v_276 : 'a }

let exec_estat  = 
  let Node { alloc = i_338_alloc; step = i_338_step ; reset = i_338_reset } = pid_estat 
   in 
  let Node { alloc = i_337_alloc; step = i_337_step ; reset = i_337_reset } = sys 
   in
  let exec_estat_alloc _ =
    ();
    { x_277 = (42.:float) ; v_276 = (42.:float);
      i_338 = i_338_alloc () (* discrete *)  ;
      i_337 = i_337_alloc () (* discrete *)  } in
  let exec_estat_reset self  =
    ((self.v_276 <- 0. ;
      self.x_277 <- 0. ; i_338_reset self.i_338  ; i_337_reset self.i_337 ):
    unit) in 
  let exec_estat_step self () =
    ((let (l_278:float) = self.v_276 in
      let (l_279:float) = self.x_277 in
      let ((error_274:float) , (u_275:float)) =
          i_338_step self.i_338 (l_279 , l_278) in
      let ((copy_322:float) , (copy_323:float)) = i_337_step self.i_337 u_275 in
      self.x_277 <- copy_322 ;
      self.v_276 <- copy_323 ; (self.x_277 , self.v_276 , error_274 , u_275)):
    float * float * float * float) in
  Node { alloc = exec_estat_alloc; reset = exec_estat_reset ;
                                   step = exec_estat_step }
type ('e , 'd , 'c , 'b , 'a) _exec_e =
  { mutable i_340 : 'e ;
    mutable i_339 : 'd ;
    mutable theta_286 : 'c ; mutable x_284 : 'b ; mutable v_283 : 'a }

let exec_e  = 
  let Node { alloc = i_340_alloc; step = i_340_step ; reset = i_340_reset } = pid_e 
   in 
  let Node { alloc = i_339_alloc; step = i_339_step ; reset = i_339_reset } = sys 
   in
  let exec_e_alloc _ =
    ();
    { theta_286 = (42.:float) ; x_284 = (42.:float) ; v_283 = (42.:float);
      i_340 = i_340_alloc () (* discrete *)  ;
      i_339 = i_339_alloc () (* discrete *)  } in
  let exec_e_reset self  =
    ((self.theta_286 <- 0. ;
      self.v_283 <- 0. ;
      self.x_284 <- 0. ; i_340_reset self.i_340  ; i_339_reset self.i_339 ):
    unit) in 
  let exec_e_step self () =
    ((let (l_289:float) = self.theta_286 in
      self.theta_286 <- (+.) l_289  (( *. ) 5.  dt) ;
      (let ((n_285:float): float) = ( *. ) 0.05  (cos self.theta_286) in
       let (n_281:float) = n_285 in
       let (l_287:float) = self.v_283 in
       let (l_288:float) = self.x_284 in
       let ((error_280:float) , (u_282:float)) =
           i_340_step self.i_340 (l_288 , l_287 , n_281) in
       let ((copy_324:float) , (copy_325:float)) =
           i_339_step self.i_339 u_282 in
       self.x_284 <- copy_324 ;
       self.v_283 <- copy_325 ;
       (let () = () in
        (self.x_284 , self.v_283 , error_280 , u_282)))):float *
                                                         float *
                                                         float * float) in
  Node { alloc = exec_e_alloc; reset = exec_e_reset ; step = exec_e_step }
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_345 : 'l ;
    mutable i_344 : 'k ;
    mutable i_343 : 'j ;
    mutable i_342 : 'i ;
    mutable i_341 : 'h ;
    mutable major_291 : 'g ;
    mutable h_298 : 'f ;
    mutable i_296 : 'e ;
    mutable h_294 : 'd ;
    mutable result_293 : 'c ; mutable x_309 : 'b ; mutable v_308 : 'a }

let main (cstate_346:Ztypes.cstate) = 
  let Node { alloc = i_345_alloc; step = i_345_step ; reset = i_345_reset } = pid 
   in 
  let Node { alloc = i_344_alloc; step = i_344_step ; reset = i_344_reset } = sys 
   in 
  let Node { alloc = i_343_alloc; step = i_343_step ; reset = i_343_reset } = exec_e 
   in 
  let Node { alloc = i_342_alloc; step = i_342_step ; reset = i_342_reset } = exec_estat 
   in 
  let Node { alloc = i_341_alloc; step = i_341_step ; reset = i_341_reset } = exec_esin 
   in
  let main_alloc _ =
    ();
    { major_291 = false ;
      h_298 = 42. ;
      i_296 = (false:bool) ;
      h_294 = (42.:float) ;
      result_293 = (():unit) ; x_309 = (42.:float) ; v_308 = (42.:float);
      i_345 = i_345_alloc () (* discrete *)  ;
      i_344 = i_344_alloc () (* discrete *)  ;
      i_343 = i_343_alloc () (* discrete *)  ;
      i_342 = i_342_alloc () (* discrete *)  ;
      i_341 = i_341_alloc () (* discrete *)  } in
  let main_step self ((time_290:float) , ()) =
    ((self.major_291 <- cstate_346.major ;
      (let (result_351:unit) =
           let h_297 = ref (infinity:float) in
           (if self.i_296 then self.h_294 <- (+.) time_290  0.) ;
           (let (z_295:bool) =
                (&&) self.major_291  ((>=) time_290  self.h_294) in
            self.h_294 <- (if z_295 then (+.) self.h_294  0.1 else self.h_294)
            ;
            h_297 := min !h_297  self.h_294 ;
            self.h_298 <- !h_297 ;
            self.i_296 <- false ;
            (let (trigger_292:zero) = z_295 in
             (begin match trigger_292 with
                    | true ->
                        let () = () in
                        let (l_310:float) = self.v_308 in
                        let (l_311:float) = self.x_309 in
                        let ((error_306:float) , (u_307:float)) =
                            i_345_step self.i_345 (l_311 , l_310) in
                        let _ = error_306 in
                        let (u_300:float) = u_307 in
                        let ((copy_326:float) , (copy_327:float)) =
                            i_344_step self.i_344 u_307 in
                        self.v_308 <- copy_327 ;
                        (let (v_301:float) = self.v_308 in
                         self.x_309 <- copy_326 ;
                         (let (x_302:float) = self.x_309 in
                          let ((x_e_303:float) , _ , _ , _) =
                              i_343_step self.i_343 () in
                          let ((x_estat_305:float) , _ , _ , _) =
                              i_342_step self.i_342 () in
                          let ((x_esin_304:float) ,
                               _ , _ , _ , (noise_299:float)) =
                              i_341_step self.i_341 () in
                          let _ = print_string "x= " in
                          let _ = print_float x_302 in
                          let _ = print_string " v= " in
                          let _ = print_float v_301 in
                          let _ = print_string " u=" in
                          let _ = print_float u_300 in
                          self.result_293 <- print_newline ()))
                    | _ -> self.result_293 <- ()  end) ; self.result_293)) in
       cstate_346.horizon <- min cstate_346.horizon  self.h_298 ; result_351)):
    unit) in 
  let main_reset self  =
    ((self.i_296 <- true ;
      self.v_308 <- 0. ;
      self.x_309 <- 0. ;
      i_345_reset self.i_345  ;
      i_344_reset self.i_344  ;
      i_343_reset self.i_343  ;
      i_342_reset self.i_342  ; i_341_reset self.i_341 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
