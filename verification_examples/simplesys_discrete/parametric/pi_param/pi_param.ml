(* The Zelus compiler, version 2.2-dev
  (2026-10-30-20:15) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = (/.) (( *. ) 0.2  1.)  dt

let ki = (/.) (( *. ) (( *. ) ((/.) 1.  36.)  kp)  ((-.) 2.  (( *. ) kp  dt)))
               dt

let calc_energyk1v2 (((energyk1_284:float): float) ,
                     ((alpha_282:float): float) ,
                     ((beta_283:float): float) ,
                     ((errork1dev_287:float): float) ,
                     ((integralk1dev_290:float): float) ,
                     ((errork1_286:float): float) ,
                     ((integralk1_289:float): float) ,
                     ((errork_285:float): float) ,
                     ((integralk_288:float): float)) =
  let ((energyk1v2_291:float): float) = energyk1_284 in
  energyk1v2_291

let calc_energyk1v2p1 (((energyk1v2p1_293:float): float) ,
                       ((alpha_292:float): float) ,
                       ((errork1dev_295:float): float) ,
                       ((errork_294:float): float) ,
                       ((integralk_296:float): float)) =
  let ((energyk1v2p1v2_297:float): float) = energyk1v2p1_293 in
  let ((energyk1v2p1vf_298:float): float) = energyk1v2p1v2_297 in
  energyk1v2p1vf_298

let calc_energyk1v2p2v3 (((energyk1v2p2v3_299:float): float) ,
                         ((integralk1dev_302:float): float) ,
                         ((errork_300:float): float) ,
                         ((integralk_301:float): float)) =
  let ((energyk1v2p2v3calc_303:float): float) = energyk1v2p2v3_299 in
  energyk1v2p2v3calc_303

let calc_energyk1v2p2 (((energyk1v2p2_305:float): float) ,
                       ((beta_304:float): float) ,
                       ((integralk1dev_308:float): float) ,
                       ((errork_306:float): float) ,
                       ((integralk_307:float): float)) =
  let ((integralk1dev_315:float): float) = integralk1dev_308 in
  let ((errork_313:float): float) = errork_306 in
  let ((integralk_314:float): float) = integralk_307 in
  let ((energyk1v2p2v2_309:float): float) = energyk1v2p2_305 in
  let ((energyk1v2p2v3_310:float): float) = energyk1v2p2v2_309 in
  let ((energyk1v2p2v3_312:float): float) = energyk1v2p2v3_310 in
  let ((energyk1v2p2v3calc_316:float): float) = energyk1v2p2v3_312 in
  let ((energyk1v2p2vf_311:float): float) = energyk1v2p2v3calc_316 in
  energyk1v2p2vf_311

let calc_energyk1vf (((energyk1_319:float): float) ,
                     ((alpha_317:float): float) ,
                     ((beta_318:float): float) ,
                     ((errork1dev_322:float): float) ,
                     ((integralk1dev_325:float): float) ,
                     ((errork1_321:float): float) ,
                     ((integralk1_324:float): float) ,
                     ((errork_320:float): float) ,
                     ((integralk_323:float): float)) =
  let ((energyk1v2_326:float): float) =
      calc_energyk1v2 (energyk1_319 ,
                       alpha_317 ,
                       beta_318 ,
                       errork1dev_322 ,
                       integralk1dev_325 ,
                       errork1_321 ,
                       integralk1_324 , errork_320 , integralk_323) in
  let ((energyk1v2p1_327:float): float) =
      ( *. ) (( *. ) alpha_317  errork1dev_322)  errork1dev_322 in
  let ((energyk1v2p1vf_328:float): float) =
      calc_energyk1v2p1 (energyk1v2p1_327 ,
                         alpha_317 ,
                         errork1dev_322 , errork_320 , integralk_323) in
  let ((energyk1v2p2_329:float): float) =
      ( *. ) (( *. ) beta_318  integralk1dev_325)  integralk1dev_325 in
  let ((energyk1v2p2vf_330:float): float) =
      calc_energyk1v2p2 (energyk1v2p2_329 ,
                         beta_318 ,
                         integralk1dev_325 , errork_320 , integralk_323) in
  let ((energyk1v3_331:float): float) =
      (+.) energyk1v2p1vf_328  energyk1v2p2vf_330 in
  let ((energyk1v4_332:float): float) = energyk1v3_331 in
  let ((energyk1vf_333:float): float) = energyk1_319 in
  energyk1vf_333

let calc_diffenergy (((energyk1vf_336:float): float) ,
                     ((energykv2_337:float): float) ,
                     ((energyk1_335:float): float) ,
                     ((energyk_334:float): float) ,
                     ((errork_338:float): float) ,
                     ((integralk_339:float): float)) =
  let ((diffenergyv1_340:float): float) = (-.) energyk1vf_336  energykv2_337 in
  let ((diffenergyv2_341:float): float) = diffenergyv1_340 in
  let ((diffenergyvf_342:float): float) = diffenergyv2_341 in
  diffenergyvf_342

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_365 : 'e ;
    mutable xk1_359 : 'd ;
    mutable integralk1_355 : 'c ;
    mutable errork1_352 : 'b ; mutable energyk1bound_348 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_365 = (false:bool) ;
      xk1_359 = (42.:float) ;
      integralk1_355 = (42.:float) ;
      errork1_352 = (42.:float) ; energyk1bound_348 = (42.:float) } in
  let exec_reset self  =
    ((self.integralk1_355 <- 0. ;
      self.errork1_352 <- 1. ; self.xk1_359 <- 0. ; self.i_365 <- true):
    unit) in 
  let exec_step self () =
    ((let (l_363:float) = self.integralk1_355 in
      let ((integralk_354:float): float) = l_363 in
      let (l_362:float) = self.errork1_352 in
      let ((errork_351:float): float) = l_362 in
      let ((uk_357:float): float) =
          (+.) (( *. ) kp  errork_351)  (( *. ) ki  integralk_354) in
      let (l_364:float) = self.xk1_359 in
      let ((xk_358:float): float) = l_364 in
      let ((copy_405:float): float) = (+.) xk_358  (( *. ) uk_357  dt) in
      self.xk1_359 <- copy_405 ;
      (let ((copy_404:float): float) = (-.) r  self.xk1_359 in
       self.errork1_352 <- copy_404 ;
       (let ((copy_403:float): float) =
            (+.) integralk_354  (( *. ) self.errork1_352  dt) in
        self.integralk1_355 <- copy_403 ;
        (let ((beta_344:float): float) = ki in
         let ((alpha_343:float): float) =
             (-.) 1.  (( *. ) (( *. ) ki  dt)  dt) in
         let ((energyk1_347:float): float) =
             (+.) (( *. ) (( *. ) alpha_343  self.errork1_352) 
                          self.errork1_352) 
                  (( *. ) (( *. ) beta_344  self.integralk1_355) 
                          self.integralk1_355) in
         let ((copy_402:float): float) = energyk1_347 in
         (if self.i_365 then self.energyk1bound_348 <- alpha_343) ;
         (let (l_361:float) = self.energyk1bound_348 in
          self.energyk1bound_348 <- copy_402 ;
          self.i_365 <- false ;
          (let ((xkbound_360:float): float) = xk_358 in
           let ((energyk_346:float): float) = l_361 in
           let ((energykv2_350:float): float) = energyk_346 in
           let ((integralk1dev_356:float): float) =
               (+.) (( *. ) (( *. ) dt  ((-.) 1.  (( *. ) kp  dt))) 
                            errork_351) 
                    (( *. ) ((-.) 1.  (( *. ) (( *. ) ki  dt)  dt)) 
                            integralk_354) in
           let ((errork1dev_353:float): float) =
               (-.) (( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_351) 
                    (( *. ) (( *. ) ki  dt)  integralk_354) in
           let ((energyk1vf_349:float): float) =
               calc_energyk1vf (energyk1_347 ,
                                alpha_343 ,
                                beta_344 ,
                                errork1dev_353 ,
                                integralk1dev_356 ,
                                self.errork1_352 ,
                                self.integralk1_355 ,
                                errork_351 , integralk_354) in
           let ((diffenergy_345:float): float) =
               calc_diffenergy (energyk1vf_349 ,
                                energykv2_350 ,
                                energyk1_347 ,
                                energyk_346 , errork_351 , integralk_354) in
           (xk_358 , uk_357 , errork_351 , integralk_354))))))):float *
                                                                float *
                                                                float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_367 : 'j ;
    mutable h_374 : 'i ;
    mutable i_372 : 'h ;
    mutable h_370 : 'g ;
    mutable result_369 : 'f ;
    mutable i_401 : 'e ;
    mutable xk1_395 : 'd ;
    mutable integralk1_391 : 'c ;
    mutable errork1_388 : 'b ; mutable energyk1bound_384 : 'a }

let main (cstate_410:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_367 = false ;
      h_374 = 42. ;
      i_372 = (false:bool) ;
      h_370 = (42.:float) ;
      result_369 = (():unit) ;
      i_401 = (false:bool) ;
      xk1_395 = (42.:float) ;
      integralk1_391 = (42.:float) ;
      errork1_388 = (42.:float) ; energyk1bound_384 = (42.:float) } in
  let main_step self ((time_366:float) , ()) =
    ((self.major_367 <- cstate_410.major ;
      (let (result_415:unit) =
           let h_373 = ref (infinity:float) in
           (if self.i_372 then self.h_370 <- (+.) time_366  0.) ;
           (let (z_371:bool) =
                (&&) self.major_367  ((>=) time_366  self.h_370) in
            self.h_370 <- (if z_371 then (+.) self.h_370  0.1 else self.h_370)
            ;
            h_373 := min !h_373  self.h_370 ;
            self.h_374 <- !h_373 ;
            self.i_372 <- false ;
            (let (trigger_368:zero) = z_371 in
             (begin match trigger_368 with
                    | true ->
                        let ((alpha_379:float): float) =
                            (-.) 1.  (( *. ) (( *. ) ki  dt)  dt) in
                        (if self.i_401 then
                         self.energyk1bound_384 <- alpha_379) ;
                        self.i_401 <- false ;
                        (let () = () in
                         let (l_399:float) = self.integralk1_391 in
                         let ((integralk_390:float): float) = l_399 in
                         let (l_398:float) = self.errork1_388 in
                         let ((errork_387:float): float) = l_398 in
                         let ((uk_393:float): float) =
                             (+.) (( *. ) kp  errork_387) 
                                  (( *. ) ki  integralk_390) in
                         let (l_400:float) = self.xk1_395 in
                         let ((xk_394:float): float) = l_400 in
                         let ((copy_409:float): float) =
                             (+.) xk_394  (( *. ) uk_393  dt) in
                         self.xk1_395 <- copy_409 ;
                         (let ((copy_408:float): float) =
                              (-.) r  self.xk1_395 in
                          self.errork1_388 <- copy_408 ;
                          (let ((copy_407:float): float) =
                               (+.) integralk_390 
                                    (( *. ) self.errork1_388  dt) in
                           self.integralk1_391 <- copy_407 ;
                           (let ((beta_380:float): float) = ki in
                            let ((energyk1_383:float): float) =
                                (+.) (( *. ) (( *. ) alpha_379 
                                                     self.errork1_388) 
                                             self.errork1_388) 
                                     (( *. ) (( *. ) beta_380 
                                                     self.integralk1_391) 
                                             self.integralk1_391) in
                            let ((copy_406:float): float) = energyk1_383 in
                            let (l_397:float) = self.energyk1bound_384 in
                            self.energyk1bound_384 <- copy_406 ;
                            (let ((xkbound_396:float): float) = xk_394 in
                             let ((energyk_382:float): float) = l_397 in
                             let ((energykv2_386:float): float) = energyk_382 in
                             let ((integralk1dev_392:float): float) =
                                 (+.) (( *. ) (( *. ) dt 
                                                      ((-.) 1. 
                                                            (( *. ) kp  dt)))
                                               errork_387) 
                                      (( *. ) ((-.) 1. 
                                                    (( *. ) (( *. ) ki  dt) 
                                                            dt)) 
                                              integralk_390) in
                             let ((errork1dev_389:float): float) =
                                 (-.) (( *. ) ((-.) 1.  (( *. ) kp  dt)) 
                                              errork_387) 
                                      (( *. ) (( *. ) ki  dt)  integralk_390) in
                             let ((energyk1vf_385:float): float) =
                                 calc_energyk1vf (energyk1_383 ,
                                                  alpha_379 ,
                                                  beta_380 ,
                                                  errork1dev_389 ,
                                                  integralk1dev_392 ,
                                                  self.errork1_388 ,
                                                  self.integralk1_391 ,
                                                  errork_387 , integralk_390) in
                             let ((diffenergy_381:float): float) =
                                 calc_diffenergy (energyk1vf_385 ,
                                                  energykv2_386 ,
                                                  energyk1_383 ,
                                                  energyk_382 ,
                                                  errork_387 , integralk_390) in
                             let (integralk_376:float) = integralk_390 in
                             let (errork_375:float) = errork_387 in
                             let (uk_377:float) = uk_393 in
                             let (xk_378:float) = xk_394 in
                             let _ = print_float xk_378 in
                             let _ = print_string "," in
                             let _ = print_float uk_377 in
                             let _ = print_string "," in
                             let _ = print_float errork_375 in
                             let _ = print_string "," in
                             let _ = print_float integralk_376 in
                             self.result_369 <- print_newline ())))))
                    | _ -> self.result_369 <- ()  end) ; self.result_369)) in
       cstate_410.horizon <- min cstate_410.horizon  self.h_374 ; result_415)):
    unit) in 
  let main_reset self  =
    ((self.i_372 <- true ;
      self.i_401 <- true ;
      self.integralk1_391 <- 0. ; self.errork1_388 <- 1. ; self.xk1_395 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
