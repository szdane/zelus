(* The Zelus compiler, version 2.2-dev
  (2026-08-31-21:11) *)
open Ztypes
let setpoint = 1.

let mass = 4.

let k = 15.

let b = 4.

let kp = 30.

let ki = 40.

let kd = 10.

let u_max = 40.

let u_min = (-40.)

let dt = 0.1

let a1 = (-.) ((/.) (( *. ) ((+.) b  kd)  dt)  mass)  3.

let a2 = (+.) 3. 
              ((/.) ((+.) (( *. ) (( *. ) (-2.)  ((+.) b  kd))  dt) 
                          (( *. ) (( *. ) ((+.) kp  k)  dt)  dt))  mass)

let a3 = (-.) ((/.) ((+.) ((-.) (( *. ) ((+.) b  kd)  dt) 
                                (( *. ) (( *. ) ((+.) kp  k)  dt)  dt)) 
                          (( *. ) (( *. ) (( *. ) ki  dt)  dt)  dt))  
                    mass)  1.

let stability_condition1 = a3

let stability_condition2 = (+.) ((+.) ((+.) 1.  a1)  a2)  a3

let stability_condition3 = (+.) ((-.) ((+.) (-1.)  a1)  a2)  a3

let stability_condition41 = (-.) ((+.) ((-.) 1.  (( *. ) a3  a3)) 
                                       (( *. ) a1  a3))  a2

let stability_condition42 = (+.) ((-.) ((-.) 1.  (( *. ) a3  a3)) 
                                       (( *. ) a1  a3))  a2

type _saturate_u_cont_sym = unit

let saturate_u_cont_sym  = 
   let saturate_u_cont_sym_alloc _ = () in
  let saturate_u_cont_sym_reset self  =
    ((()):unit) in 
  let saturate_u_cont_sym_step self ((u_242:float): float) =
    ((let (u_sat_243:float) = ( *. ) 40.  (tanh ((/.) u_242  40.)) in
      u_sat_243):float) in
  Node { alloc = saturate_u_cont_sym_alloc; reset = saturate_u_cont_sym_reset
                                            ; step = saturate_u_cont_sym_step }
type ('a) _noise =
  { mutable theta_245 : 'a }

let noise  = 
   let noise_alloc _ =
     ();{ theta_245 = (42.:float) } in
  let noise_reset self  =
    (self.theta_245 <- 0.:unit) in 
  let noise_step self () =
    ((let (l_246:float) = self.theta_245 in
      self.theta_245 <- (+.) l_246  (( *. ) 5.  dt) ;
      (let ((n_244:float): float) = ( *. ) 0.05  (cos self.theta_245) in
       n_244)):float) in
  Node { alloc = noise_alloc; reset = noise_reset ; step = noise_step }
type ('b , 'a) _sys =
  { mutable x_249 : 'b ; mutable spd_248 : 'a }

let sys  = 
   let sys_alloc _ =
     ();{ x_249 = (42.:float) ; spd_248 = (42.:float) } in
  let sys_reset self  =
    ((self.x_249 <- 0. ; self.spd_248 <- 0.):unit) in 
  let sys_step self ((u_247:float): float) =
    ((let (l_250:float) = self.spd_248 in
      let (l_251:float) = self.x_249 in
      let ((copy_363:float): float) = (+.) l_251  (( *. ) l_250  dt) in
      self.x_249 <- copy_363 ;
      (let ((copy_362:float): float) =
           (+.) l_250 
                ((/.) (( *. ) ((+.) ((-.) (( *. ) ((~-.) k)  l_251) 
                                          (( *. ) b  l_250))  u_247)  
                              dt)  mass) in
       self.spd_248 <- copy_362 ; (self.x_249 , self.spd_248))):float * float) in
  Node { alloc = sys_alloc; reset = sys_reset ; step = sys_step }
type ('b , 'a) _pid =
  { mutable i_384 : 'b ; mutable integral_antiwindup_255 : 'a }

let pid  = 
  let Node { alloc = i_384_alloc; step = i_384_step ; reset = i_384_reset } = saturate_u_cont_sym 
   in
  let pid_alloc _ =
    ();
    { integral_antiwindup_255 = (42.:float);
      i_384 = i_384_alloc () (* discrete *)  } in
  let pid_reset self  =
    ((self.integral_antiwindup_255 <- 0. ; i_384_reset self.i_384 ):unit) in 
  let pid_step self (((x_253:float): float) , ((spd_252:float): float)) =
    ((let ((error_254:float): float) = (-.) setpoint  x_253 in
      let (l_258:float) = self.integral_antiwindup_255 in
      let ((u_256:float): float) =
          (-.) ((+.) (( *. ) kp  error_254)  (( *. ) ki  l_258)) 
               (( *. ) kd  spd_252) in
      let ((copy_364:float): float) =
          if (||) ((&&) ((>) u_256  u_max)  ((>) error_254  0.)) 
                  ((&&) ((<) u_256  u_min)  ((<) error_254  0.))
          then l_258
          else (+.) l_258  (( *. ) dt  error_254) in
      self.integral_antiwindup_255 <- copy_364 ;
      (let ((u_sat_257:float): float) = i_384_step self.i_384 u_256 in
       (error_254 , u_256))):float * float) in
  Node { alloc = pid_alloc; reset = pid_reset ; step = pid_step }
type ('b , 'a) _pid_esin =
  { mutable i_385 : 'b ; mutable integral_antiwindup_263 : 'a }

let pid_esin  = 
  let Node { alloc = i_385_alloc; step = i_385_step ; reset = i_385_reset } = saturate_u_cont_sym 
   in
  let pid_esin_alloc _ =
    ();
    { integral_antiwindup_263 = (42.:float);
      i_385 = i_385_alloc () (* discrete *)  } in
  let pid_esin_reset self  =
    ((self.integral_antiwindup_263 <- 0. ; i_385_reset self.i_385 ):unit) in 
  let pid_esin_step self (((x_261:float): float) ,
                          ((spd_260:float): float) ,
                          ((noise_259:float): float)) =
    ((let ((error_262:float): float) = (-.) setpoint  ((+.) x_261  noise_259) in
      let (l_266:float) = self.integral_antiwindup_263 in
      let ((u_264:float): float) =
          (-.) ((+.) (( *. ) kp  error_262)  (( *. ) ki  l_266)) 
               (( *. ) kd  ((+.) spd_260  0.)) in
      let ((copy_365:float): float) =
          if (||) ((&&) ((>) u_264  u_max)  ((>) error_262  0.)) 
                  ((&&) ((<) u_264  u_min)  ((<) error_262  0.))
          then l_266
          else (+.) l_266  (( *. ) dt  error_262) in
      self.integral_antiwindup_263 <- copy_365 ;
      (let ((u_sat_265:float): float) = i_385_step self.i_385 u_264 in
       (error_262 , u_sat_265))):float * float) in
  Node { alloc = pid_esin_alloc; reset = pid_esin_reset ;
                                 step = pid_esin_step }
type ('b , 'a) _pid_estat =
  { mutable i_386 : 'b ; mutable integral_antiwindup_270 : 'a }

let pid_estat  = 
  let Node { alloc = i_386_alloc; step = i_386_step ; reset = i_386_reset } = saturate_u_cont_sym 
   in
  let pid_estat_alloc _ =
    ();
    { integral_antiwindup_270 = (42.:float);
      i_386 = i_386_alloc () (* discrete *)  } in
  let pid_estat_reset self  =
    ((self.integral_antiwindup_270 <- 0. ; i_386_reset self.i_386 ):unit) in 
  let pid_estat_step self (((x_268:float): float) , ((spd_267:float): float)) =
    ((let ((error_269:float): float) = (-.) setpoint  ((-.) x_268  0.5) in
      let (l_273:float) = self.integral_antiwindup_270 in
      let ((u_271:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_269)  (( *. ) ki  l_273)) 
                     (( *. ) kd  ((+.) spd_267  0.)))  0. in
      let ((copy_366:float): float) =
          if (||) ((&&) ((>) u_271  u_max)  ((>) error_269  0.)) 
                  ((&&) ((<) u_271  u_min)  ((<) error_269  0.))
          then l_273
          else (+.) l_273  (( *. ) dt  error_269) in
      self.integral_antiwindup_270 <- copy_366 ;
      (let ((u_sat_272:float): float) = i_386_step self.i_386 u_271 in
       (error_269 , u_sat_272))):float * float) in
  Node { alloc = pid_estat_alloc; reset = pid_estat_reset ;
                                  step = pid_estat_step }
type ('b , 'a) _pid_e =
  { mutable i_387 : 'b ; mutable integral_antiwindup_278 : 'a }

let pid_e  = 
  let Node { alloc = i_387_alloc; step = i_387_step ; reset = i_387_reset } = saturate_u_cont_sym 
   in
  let pid_e_alloc _ =
    ();
    { integral_antiwindup_278 = (42.:float);
      i_387 = i_387_alloc () (* discrete *)  } in
  let pid_e_reset self  =
    ((self.integral_antiwindup_278 <- 0. ; i_387_reset self.i_387 ):unit) in 
  let pid_e_step self (((x_276:float): float) ,
                       ((spd_275:float): float) , ((noise_274:float): float)) =
    ((let ((error_277:float): float) =
          (-.) setpoint  ((-.) ((+.) x_276  noise_274)  0.5) in
      let (l_281:float) = self.integral_antiwindup_278 in
      let ((u_279:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_277)  (( *. ) ki  l_281)) 
                     (( *. ) kd  ((+.) spd_275  0.)))  noise_274 in
      let ((copy_367:float): float) =
          if (||) ((&&) ((>) u_279  u_max)  ((>) error_277  0.)) 
                  ((&&) ((<) u_279  u_min)  ((<) error_277  0.))
          then l_281
          else (+.) l_281  (( *. ) dt  error_277) in
      self.integral_antiwindup_278 <- copy_367 ;
      (let ((u_sat_280:float): float) = i_387_step self.i_387 u_279 in
       (error_277 , u_sat_280))):float * float) in
  Node { alloc = pid_e_alloc; reset = pid_e_reset ; step = pid_e_step }
type ('d , 'c , 'b , 'a) _exec =
  { mutable i_389 : 'd ;
    mutable i_388 : 'c ; mutable x_285 : 'b ; mutable spd_283 : 'a }

let exec  = 
  let Node { alloc = i_389_alloc; step = i_389_step ; reset = i_389_reset } = pid 
   in 
  let Node { alloc = i_388_alloc; step = i_388_step ; reset = i_388_reset } = sys 
   in
  let exec_alloc _ =
    ();
    { x_285 = (42.:float) ; spd_283 = (42.:float);
      i_389 = i_389_alloc () (* discrete *)  ;
      i_388 = i_388_alloc () (* discrete *)  } in
  let exec_reset self  =
    ((self.spd_283 <- 0. ;
      self.x_285 <- 0. ; i_389_reset self.i_389  ; i_388_reset self.i_388 ):
    unit) in 
  let exec_step self () =
    ((let (l_286:float) = self.spd_283 in
      let (l_287:float) = self.x_285 in
      let ((error_282:float) , (u_284:float)) =
          i_389_step self.i_389 (l_287 , l_286) in
      let ((copy_368:float) , (copy_369:float)) = i_388_step self.i_388 u_284 in
      self.x_285 <- copy_368 ;
      self.spd_283 <- copy_369 ;
      (self.x_285 , self.spd_283 , error_282 , u_284)):float *
                                                       float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('e , 'd , 'c , 'b , 'a) _exec_esin =
  { mutable i_391 : 'e ;
    mutable i_390 : 'd ;
    mutable theta_294 : 'c ; mutable x_292 : 'b ; mutable spd_290 : 'a }

let exec_esin  = 
  let Node { alloc = i_391_alloc; step = i_391_step ; reset = i_391_reset } = pid_esin 
   in 
  let Node { alloc = i_390_alloc; step = i_390_step ; reset = i_390_reset } = sys 
   in
  let exec_esin_alloc _ =
    ();
    { theta_294 = (42.:float) ; x_292 = (42.:float) ; spd_290 = (42.:float);
      i_391 = i_391_alloc () (* discrete *)  ;
      i_390 = i_390_alloc () (* discrete *)  } in
  let exec_esin_reset self  =
    ((self.theta_294 <- 0. ;
      self.spd_290 <- 0. ;
      self.x_292 <- 0. ; i_391_reset self.i_391  ; i_390_reset self.i_390 ):
    unit) in 
  let exec_esin_step self () =
    ((let (l_297:float) = self.theta_294 in
      self.theta_294 <- (+.) l_297  (( *. ) 5.  dt) ;
      (let ((n_293:float): float) = ( *. ) 0.05  (cos self.theta_294) in
       let (n_289:float) = n_293 in
       let (l_295:float) = self.spd_290 in
       let (l_296:float) = self.x_292 in
       let ((error_288:float) , (u_291:float)) =
           i_391_step self.i_391 (l_296 , l_295 , n_289) in
       let ((copy_370:float) , (copy_371:float)) =
           i_390_step self.i_390 u_291 in
       self.x_292 <- copy_370 ;
       self.spd_290 <- copy_371 ;
       (let () = () in
        (self.x_292 , self.spd_290 , error_288 , u_291 , n_289)))):float *
                                                                   float *
                                                                   float *
                                                                   float *
                                                                   float) in
  Node { alloc = exec_esin_alloc; reset = exec_esin_reset ;
                                  step = exec_esin_step }
type ('d , 'c , 'b , 'a) _exec_estat =
  { mutable i_393 : 'd ;
    mutable i_392 : 'c ; mutable x_301 : 'b ; mutable spd_299 : 'a }

let exec_estat  = 
  let Node { alloc = i_393_alloc; step = i_393_step ; reset = i_393_reset } = pid_estat 
   in 
  let Node { alloc = i_392_alloc; step = i_392_step ; reset = i_392_reset } = sys 
   in
  let exec_estat_alloc _ =
    ();
    { x_301 = (42.:float) ; spd_299 = (42.:float);
      i_393 = i_393_alloc () (* discrete *)  ;
      i_392 = i_392_alloc () (* discrete *)  } in
  let exec_estat_reset self  =
    ((self.spd_299 <- 0. ;
      self.x_301 <- 0. ; i_393_reset self.i_393  ; i_392_reset self.i_392 ):
    unit) in 
  let exec_estat_step self () =
    ((let (l_302:float) = self.spd_299 in
      let (l_303:float) = self.x_301 in
      let ((error_298:float) , (u_300:float)) =
          i_393_step self.i_393 (l_303 , l_302) in
      let ((copy_372:float) , (copy_373:float)) = i_392_step self.i_392 u_300 in
      self.x_301 <- copy_372 ;
      self.spd_299 <- copy_373 ;
      (self.x_301 , self.spd_299 , error_298 , u_300)):float *
                                                       float * float * float) in
  Node { alloc = exec_estat_alloc; reset = exec_estat_reset ;
                                   step = exec_estat_step }
type ('e , 'd , 'c , 'b , 'a) _exec_e =
  { mutable i_395 : 'e ;
    mutable i_394 : 'd ;
    mutable theta_310 : 'c ; mutable x_308 : 'b ; mutable spd_306 : 'a }

let exec_e  = 
  let Node { alloc = i_395_alloc; step = i_395_step ; reset = i_395_reset } = pid_e 
   in 
  let Node { alloc = i_394_alloc; step = i_394_step ; reset = i_394_reset } = sys 
   in
  let exec_e_alloc _ =
    ();
    { theta_310 = (42.:float) ; x_308 = (42.:float) ; spd_306 = (42.:float);
      i_395 = i_395_alloc () (* discrete *)  ;
      i_394 = i_394_alloc () (* discrete *)  } in
  let exec_e_reset self  =
    ((self.theta_310 <- 0. ;
      self.spd_306 <- 0. ;
      self.x_308 <- 0. ; i_395_reset self.i_395  ; i_394_reset self.i_394 ):
    unit) in 
  let exec_e_step self () =
    ((let (l_313:float) = self.theta_310 in
      self.theta_310 <- (+.) l_313  (( *. ) 5.  dt) ;
      (let ((n_309:float): float) = ( *. ) 0.05  (cos self.theta_310) in
       let (n_305:float) = n_309 in
       let (l_311:float) = self.spd_306 in
       let (l_312:float) = self.x_308 in
       let ((error_304:float) , (u_307:float)) =
           i_395_step self.i_395 (l_312 , l_311 , n_305) in
       let ((copy_374:float) , (copy_375:float)) =
           i_394_step self.i_394 u_307 in
       self.x_308 <- copy_374 ;
       self.spd_306 <- copy_375 ;
       (let () = () in
        (self.x_308 , self.spd_306 , error_304 , u_307)))):float *
                                                           float *
                                                           float * float) in
  Node { alloc = exec_e_alloc; reset = exec_e_reset ; step = exec_e_step }
type ('w ,
      'v ,
      'u ,
      't ,
      's ,
      'r ,
      'q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_403 : 'w ;
    mutable i_402 : 'v ;
    mutable i_401 : 'u ;
    mutable i_400 : 't ;
    mutable i_399 : 's ;
    mutable i_398 : 'r ;
    mutable i_397 : 'q ;
    mutable i_396 : 'p ;
    mutable major_315 : 'o ;
    mutable h_322 : 'n ;
    mutable i_320 : 'm ;
    mutable h_318 : 'l ;
    mutable result_317 : 'k ;
    mutable theta_351 : 'j ;
    mutable x_349 : 'i ;
    mutable spd_347 : 'h ;
    mutable x_344 : 'g ;
    mutable spd_342 : 'f ;
    mutable theta_340 : 'e ;
    mutable x_338 : 'd ;
    mutable spd_336 : 'c ; mutable x_333 : 'b ; mutable spd_331 : 'a }

let main (cstate_404:Ztypes.cstate) = 
  let Node { alloc = i_403_alloc; step = i_403_step ; reset = i_403_reset } = pid_e 
   in 
  let Node { alloc = i_402_alloc; step = i_402_step ; reset = i_402_reset } = sys 
   in 
  let Node { alloc = i_401_alloc; step = i_401_step ; reset = i_401_reset } = pid_estat 
   in 
  let Node { alloc = i_400_alloc; step = i_400_step ; reset = i_400_reset } = sys 
   in 
  let Node { alloc = i_399_alloc; step = i_399_step ; reset = i_399_reset } = pid_esin 
   in 
  let Node { alloc = i_398_alloc; step = i_398_step ; reset = i_398_reset } = sys 
   in 
  let Node { alloc = i_397_alloc; step = i_397_step ; reset = i_397_reset } = pid 
   in 
  let Node { alloc = i_396_alloc; step = i_396_step ; reset = i_396_reset } = sys 
   in
  let main_alloc _ =
    ();
    { major_315 = false ;
      h_322 = 42. ;
      i_320 = (false:bool) ;
      h_318 = (42.:float) ;
      result_317 = (():unit) ;
      theta_351 = (42.:float) ;
      x_349 = (42.:float) ;
      spd_347 = (42.:float) ;
      x_344 = (42.:float) ;
      spd_342 = (42.:float) ;
      theta_340 = (42.:float) ;
      x_338 = (42.:float) ;
      spd_336 = (42.:float) ; x_333 = (42.:float) ; spd_331 = (42.:float);
      i_403 = i_403_alloc () (* discrete *)  ;
      i_402 = i_402_alloc () (* discrete *)  ;
      i_401 = i_401_alloc () (* discrete *)  ;
      i_400 = i_400_alloc () (* discrete *)  ;
      i_399 = i_399_alloc () (* discrete *)  ;
      i_398 = i_398_alloc () (* discrete *)  ;
      i_397 = i_397_alloc () (* discrete *)  ;
      i_396 = i_396_alloc () (* discrete *)  } in
  let main_step self ((time_314:float) , ()) =
    ((self.major_315 <- cstate_404.major ;
      (let (result_409:unit) =
           let h_321 = ref (infinity:float) in
           (if self.i_320 then self.h_318 <- (+.) time_314  0.) ;
           (let (z_319:bool) =
                (&&) self.major_315  ((>=) time_314  self.h_318) in
            self.h_318 <- (if z_319 then (+.) self.h_318  0.1 else self.h_318)
            ;
            h_321 := min !h_321  self.h_318 ;
            self.h_322 <- !h_321 ;
            self.i_320 <- false ;
            (let (trigger_316:zero) = z_319 in
             (begin match trigger_316 with
                    | true ->
                        let () = () in
                        let () = () in
                        let (l_361:float) = self.theta_351 in
                        self.theta_351 <- (+.) l_361  (( *. ) 5.  dt) ;
                        (let ((n_350:float): float) =
                             ( *. ) 0.05  (cos self.theta_351) in
                         let (n_346:float) = n_350 in
                         let (l_359:float) = self.spd_347 in
                         let (l_360:float) = self.x_349 in
                         let ((error_345:float) , (u_348:float)) =
                             i_403_step self.i_403 (l_360 , l_359 , n_346) in
                         let ((copy_376:float) , (copy_377:float)) =
                             i_402_step self.i_402 u_348 in
                         self.spd_347 <- copy_377 ;
                         (let _ = self.spd_347 in
                          let _ = error_345 in
                          let _ = u_348 in
                          let () = () in
                          let (l_357:float) = self.spd_342 in
                          let (l_358:float) = self.x_344 in
                          let ((error_341:float) , (u_343:float)) =
                              i_401_step self.i_401 (l_358 , l_357) in
                          let ((copy_378:float) , (copy_379:float)) =
                              i_400_step self.i_400 u_343 in
                          self.spd_342 <- copy_379 ;
                          (let _ = self.spd_342 in
                           let _ = error_341 in
                           let _ = u_343 in
                           let () = () in
                           let () = () in
                           let (l_356:float) = self.theta_340 in
                           self.theta_340 <- (+.) l_356  (( *. ) 5.  dt) ;
                           (let ((n_339:float): float) =
                                ( *. ) 0.05  (cos self.theta_340) in
                            let (n_335:float) = n_339 in
                            let (l_354:float) = self.spd_336 in
                            let (l_355:float) = self.x_338 in
                            let ((error_334:float) , (u_337:float)) =
                                i_399_step self.i_399 (l_355 , l_354 , n_335) in
                            let ((copy_380:float) , (copy_381:float)) =
                                i_398_step self.i_398 u_337 in
                            self.spd_336 <- copy_381 ;
                            (let _ = self.spd_336 in
                             let _ = error_334 in
                             let _ = u_337 in
                             let () = () in
                             let (l_352:float) = self.spd_331 in
                             let (l_353:float) = self.x_333 in
                             let ((error_330:float) , (u_332:float)) =
                                 i_397_step self.i_397 (l_353 , l_352) in
                             let _ = error_330 in
                             self.x_349 <- copy_376 ;
                             (let (x_e_327:float) = self.x_349 in
                              self.x_344 <- copy_378 ;
                              (let (x_estat_329:float) = self.x_344 in
                               let (noise_323:float) = n_335 in
                               self.x_338 <- copy_380 ;
                               (let (x_esin_328:float) = self.x_338 in
                                let (u_325:float) = u_332 in
                                let ((copy_382:float) , (copy_383:float)) =
                                    i_396_step self.i_396 u_332 in
                                self.spd_331 <- copy_383 ;
                                (let (spd_324:float) = self.spd_331 in
                                 self.x_333 <- copy_382 ;
                                 (let (x_326:float) = self.x_333 in
                                  let _ = print_float x_326 in
                                  let _ = print_string "," in
                                  let _ = print_float spd_324 in
                                  let _ = print_string "," in
                                  let _ = print_float u_325 in
                                  let _ = print_string "," in
                                  let _ = print_float x_esin_328 in
                                  let _ = print_string "," in
                                  let _ = print_float noise_323 in
                                  let _ = print_string "," in
                                  let _ = print_float x_estat_329 in
                                  let _ = print_string "," in
                                  let _ = print_float x_e_327 in
                                  self.result_317 <- print_newline ()))))))))))
                    | _ -> self.result_317 <- ()  end) ; self.result_317)) in
       cstate_404.horizon <- min cstate_404.horizon  self.h_322 ; result_409)):
    unit) in 
  let main_reset self  =
    ((self.i_320 <- true ;
      self.theta_351 <- 0. ;
      self.spd_347 <- 0. ;
      self.x_349 <- 0. ;
      i_403_reset self.i_403  ;
      i_402_reset self.i_402  ;
      self.spd_342 <- 0. ;
      self.x_344 <- 0. ;
      i_401_reset self.i_401  ;
      i_400_reset self.i_400  ;
      self.theta_340 <- 0. ;
      self.spd_336 <- 0. ;
      self.x_338 <- 0. ;
      i_399_reset self.i_399  ;
      i_398_reset self.i_398  ;
      self.spd_331 <- 0. ;
      self.x_333 <- 0. ; i_397_reset self.i_397  ; i_396_reset self.i_396 ):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
