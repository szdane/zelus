(* The Zelus compiler, version 2.2-dev
  (2026-11-19-21:13) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = (/.) (( *. ) 0.2  1.)  dt

let ki = (/.) ((-.) ((/.) (( *. ) 2.  kp)  dt)  (( *. ) kp  kp))  36.

let x0 = 0.

let error0 = (-.) r  x0

let calc_energyk1v2 (((energyk1_287:float): float) ,
                     ((alpha_285:float): float) ,
                     ((beta_286:float): float) ,
                     ((errork1dev_290:float): float) ,
                     ((integralk1dev_293:float): float) ,
                     ((errork1_289:float): float) ,
                     ((integralk1_292:float): float) ,
                     ((errork_288:float): float) ,
                     ((integralk_291:float): float)) =
  let ((energyk1v2_294:float): float) = energyk1_287 in
  energyk1v2_294

let calc_energyk1v2p1 (((energyk1v2p1_296:float): float) ,
                       ((alpha_295:float): float) ,
                       ((errork1dev_298:float): float) ,
                       ((errork_297:float): float) ,
                       ((integralk_299:float): float)) =
  let ((energyk1v2p1v2_300:float): float) = energyk1v2p1_296 in
  let ((energyk1v2p1vf_301:float): float) = energyk1v2p1v2_300 in
  energyk1v2p1vf_301

let calc_energyk1v2p2 (((energyk1v2p2_303:float): float) ,
                       ((beta_302:float): float) ,
                       ((integralk1dev_306:float): float) ,
                       ((errork_304:float): float) ,
                       ((integralk_305:float): float)) =
  let ((energyk1v2p2v2_307:float): float) = energyk1v2p2_303 in
  let ((energyk1v2p2v3_308:float): float) = energyk1v2p2v2_307 in
  let ((energyk1v2p2vf_309:float): float) = energyk1v2p2v3_308 in
  energyk1v2p2vf_309

let calc_energyk1vf (((energyk1_312:float): float) ,
                     ((alpha_310:float): float) ,
                     ((beta_311:float): float) ,
                     ((errork1dev_315:float): float) ,
                     ((integralk1dev_318:float): float) ,
                     ((errork1_314:float): float) ,
                     ((integralk1_317:float): float) ,
                     ((errork_313:float): float) ,
                     ((integralk_316:float): float)) =
  let ((energyk1v2_319:float): float) =
      calc_energyk1v2 (energyk1_312 ,
                       alpha_310 ,
                       beta_311 ,
                       errork1dev_315 ,
                       integralk1dev_318 ,
                       errork1_314 ,
                       integralk1_317 , errork_313 , integralk_316) in
  let ((alpha_327:float): float) = alpha_310 in
  let ((errork1dev_330:float): float) = errork1dev_315 in
  let ((errork_329:float): float) = errork_313 in
  let ((integralk_331:float): float) = integralk_316 in
  let ((beta_334:float): float) = beta_311 in
  let ((integralk1dev_338:float): float) = integralk1dev_318 in
  let ((errork_336:float): float) = errork_313 in
  let ((integralk_337:float): float) = integralk_316 in
  let ((energyk1v2p1_320:float): float) =
      ( *. ) (( *. ) alpha_310  errork1dev_315)  errork1dev_315 in
  let ((energyk1v2p1_328:float): float) = energyk1v2p1_320 in
  let ((energyk1v2p1v2_332:float): float) = energyk1v2p1_328 in
  let ((energyk1v2p1vf_333:float): float) = energyk1v2p1v2_332 in
  let ((energyk1v2p1vf_321:float): float) = energyk1v2p1vf_333 in
  let ((energyk1v2p2_322:float): float) =
      ( *. ) (( *. ) beta_311  integralk1dev_318)  integralk1dev_318 in
  let ((energyk1v2p2_335:float): float) = energyk1v2p2_322 in
  let ((energyk1v2p2v2_339:float): float) = energyk1v2p2_335 in
  let ((energyk1v2p2v3_340:float): float) = energyk1v2p2v2_339 in
  let ((energyk1v2p2vf_341:float): float) = energyk1v2p2v3_340 in
  let ((energyk1v2p2vf_323:float): float) = energyk1v2p2vf_341 in
  let ((energyk1v3_324:float): float) =
      (+.) energyk1v2p1vf_321  energyk1v2p2vf_323 in
  let ((energyk1v4_325:float): float) = energyk1v3_324 in
  let ((energyk1vf_326:float): float) = energyk1v4_325 in
  energyk1vf_326

let calc_diffenergy (((energyk1vf_344:float): float) ,
                     ((energykv2_345:float): float) ,
                     ((energyk1_343:float): float) ,
                     ((energyk_342:float): float) ,
                     ((errork_346:float): float) ,
                     ((integralk_347:float): float)) =
  let ((diffenergyv1_348:float): float) = (-.) energyk1vf_344  energykv2_345 in
  let ((diffenergyv2_349:float): float) = diffenergyv1_348 in
  let ((diffenergyvf_350:float): float) = diffenergyv2_349 in
  diffenergyvf_350

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_375 : 'e ;
    mutable xk1_369 : 'd ;
    mutable integralk1_365 : 'c ;
    mutable errork1_362 : 'b ; mutable energyk1bound_356 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_375 = (false:bool) ;
      xk1_369 = (42.:float) ;
      integralk1_365 = (42.:float) ;
      errork1_362 = (42.:float) ; energyk1bound_356 = (42.:float) } in
  let exec_reset self  =
    ((self.integralk1_365 <- 0. ; self.i_375 <- true):unit) in 
  let exec_step self () =
    ((let (l_373:float) = self.integralk1_365 in
      let ((integralk_364:float): float) = l_373 in
      (if self.i_375 then self.errork1_362 <- error0) ;
      (let (l_372:float) = self.errork1_362 in
       let ((errork_361:float): float) = l_372 in
       let ((uk_367:float): float) =
           (+.) (( *. ) kp  errork_361)  (( *. ) ki  integralk_364) in
       (if self.i_375 then self.xk1_369 <- x0) ;
       (let (l_374:float) = self.xk1_369 in
        let ((xk_368:float): float) = l_374 in
        let ((copy_417:float): float) = (+.) xk_368  (( *. ) uk_367  dt) in
        self.xk1_369 <- copy_417 ;
        (let ((copy_416:float): float) = (-.) r  self.xk1_369 in
         self.errork1_362 <- copy_416 ;
         (let ((copy_415:float): float) =
              (+.) integralk_364  (( *. ) self.errork1_362  dt) in
          self.integralk1_365 <- copy_415 ;
          (let ((beta_352:float): float) = ki in
           let ((alpha_351:float): float) =
               (-.) 1.  (( *. ) (( *. ) ki  dt)  dt) in
           let ((energyk1_355:float): float) =
               (+.) (( *. ) (( *. ) alpha_351  self.errork1_362) 
                            self.errork1_362) 
                    (( *. ) (( *. ) beta_352  self.integralk1_365) 
                            self.integralk1_365) in
           let ((copy_414:float): float) = energyk1_355 in
           (if self.i_375 then
            self.energyk1bound_356 <- ( *. ) alpha_351  (( ** ) error0  2.))
           ;
           (let (l_371:float) = self.energyk1bound_356 in
            self.energyk1bound_356 <- copy_414 ;
            self.i_375 <- false ;
            (let ((xkbound_370:float): float) = xk_368 in
             let ((energykbound2_359:float): float) =
                 (+.) (( *. ) (( *. ) ((-.) 1.  (( *. ) (( *. ) ki  dt)  dt))
                                       errork_361)  errork_361) 
                      (( *. ) (( *. ) ki  integralk_364)  integralk_364) in
             let ((energyk_354:float): float) = l_371 in
             let ((energykbound_358:float): float) = energyk_354 in
             let ((integralk1dev_366:float): float) =
                 (+.) (( *. ) (( *. ) dt  ((-.) 1.  (( *. ) kp  dt))) 
                              errork_361) 
                      (( *. ) ((-.) 1.  (( *. ) (( *. ) ki  dt)  dt)) 
                              integralk_364) in
             let ((errork1dev_363:float): float) =
                 (-.) (( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_361) 
                      (( *. ) (( *. ) ki  dt)  integralk_364) in
             let ((energyk1vf_357:float): float) =
                 calc_energyk1vf (energyk1_355 ,
                                  alpha_351 ,
                                  beta_352 ,
                                  errork1dev_363 ,
                                  integralk1dev_366 ,
                                  self.errork1_362 ,
                                  self.integralk1_365 ,
                                  errork_361 , integralk_364) in
             let ((energykv2_360:float): float) = energyk_354 in
             let ((diffenergy_353:float): float) =
                 calc_diffenergy (energyk1vf_357 ,
                                  energykv2_360 ,
                                  energyk1_355 ,
                                  energyk_354 , errork_361 , integralk_364) in
             (xk_368 , uk_367 , errork_361 , integralk_364))))))))):float *
                                                                    float *
                                                                    float *
                                                                    float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_377 : 'j ;
    mutable h_384 : 'i ;
    mutable i_382 : 'h ;
    mutable h_380 : 'g ;
    mutable result_379 : 'f ;
    mutable i_413 : 'e ;
    mutable xk1_407 : 'd ;
    mutable integralk1_403 : 'c ;
    mutable errork1_400 : 'b ; mutable energyk1bound_394 : 'a }

let main (cstate_422:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_377 = false ;
      h_384 = 42. ;
      i_382 = (false:bool) ;
      h_380 = (42.:float) ;
      result_379 = (():unit) ;
      i_413 = (false:bool) ;
      xk1_407 = (42.:float) ;
      integralk1_403 = (42.:float) ;
      errork1_400 = (42.:float) ; energyk1bound_394 = (42.:float) } in
  let main_step self ((time_376:float) , ()) =
    ((self.major_377 <- cstate_422.major ;
      (let (result_427:unit) =
           let h_383 = ref (infinity:float) in
           (if self.i_382 then self.h_380 <- (+.) time_376  0.) ;
           (let (z_381:bool) =
                (&&) self.major_377  ((>=) time_376  self.h_380) in
            self.h_380 <- (if z_381 then (+.) self.h_380  0.1 else self.h_380)
            ;
            h_383 := min !h_383  self.h_380 ;
            self.h_384 <- !h_383 ;
            self.i_382 <- false ;
            (let (trigger_378:zero) = z_381 in
             (begin match trigger_378 with
                    | true ->
                        let ((alpha_389:float): float) =
                            (-.) 1.  (( *. ) (( *. ) ki  dt)  dt) in
                        (if self.i_413 then
                         self.energyk1bound_394 <- ( *. ) alpha_389 
                                                          (( ** ) error0  2.))
                        ;
                        (if self.i_413 then self.errork1_400 <- error0) ;
                        (if self.i_413 then self.xk1_407 <- x0) ;
                        self.i_413 <- false ;
                        (let () = () in
                         let (l_411:float) = self.integralk1_403 in
                         let ((integralk_402:float): float) = l_411 in
                         let (l_410:float) = self.errork1_400 in
                         let ((errork_399:float): float) = l_410 in
                         let ((uk_405:float): float) =
                             (+.) (( *. ) kp  errork_399) 
                                  (( *. ) ki  integralk_402) in
                         let (l_412:float) = self.xk1_407 in
                         let ((xk_406:float): float) = l_412 in
                         let ((copy_421:float): float) =
                             (+.) xk_406  (( *. ) uk_405  dt) in
                         self.xk1_407 <- copy_421 ;
                         (let ((copy_420:float): float) =
                              (-.) r  self.xk1_407 in
                          self.errork1_400 <- copy_420 ;
                          (let ((copy_419:float): float) =
                               (+.) integralk_402 
                                    (( *. ) self.errork1_400  dt) in
                           self.integralk1_403 <- copy_419 ;
                           (let ((beta_390:float): float) = ki in
                            let ((energyk1_393:float): float) =
                                (+.) (( *. ) (( *. ) alpha_389 
                                                     self.errork1_400) 
                                             self.errork1_400) 
                                     (( *. ) (( *. ) beta_390 
                                                     self.integralk1_403) 
                                             self.integralk1_403) in
                            let ((copy_418:float): float) = energyk1_393 in
                            let (l_409:float) = self.energyk1bound_394 in
                            self.energyk1bound_394 <- copy_418 ;
                            (let ((xkbound_408:float): float) = xk_406 in
                             let ((energykbound2_397:float): float) =
                                 (+.) (( *. ) (( *. ) ((-.) 1. 
                                                            (( *. ) (
                                                                    ( *. ) 
                                                                    ki  dt) 
                                                                    dt)) 
                                                      errork_399)  errork_399)
                                      
                                      (( *. ) (( *. ) ki  integralk_402) 
                                              integralk_402) in
                             let ((energyk_392:float): float) = l_409 in
                             let ((energykbound_396:float): float) =
                                 energyk_392 in
                             let ((integralk1dev_404:float): float) =
                                 (+.) (( *. ) (( *. ) dt 
                                                      ((-.) 1. 
                                                            (( *. ) kp  dt)))
                                               errork_399) 
                                      (( *. ) ((-.) 1. 
                                                    (( *. ) (( *. ) ki  dt) 
                                                            dt)) 
                                              integralk_402) in
                             let ((errork1dev_401:float): float) =
                                 (-.) (( *. ) ((-.) 1.  (( *. ) kp  dt)) 
                                              errork_399) 
                                      (( *. ) (( *. ) ki  dt)  integralk_402) in
                             let ((energyk1vf_395:float): float) =
                                 calc_energyk1vf (energyk1_393 ,
                                                  alpha_389 ,
                                                  beta_390 ,
                                                  errork1dev_401 ,
                                                  integralk1dev_404 ,
                                                  self.errork1_400 ,
                                                  self.integralk1_403 ,
                                                  errork_399 , integralk_402) in
                             let ((energykv2_398:float): float) = energyk_392 in
                             let ((diffenergy_391:float): float) =
                                 calc_diffenergy (energyk1vf_395 ,
                                                  energykv2_398 ,
                                                  energyk1_393 ,
                                                  energyk_392 ,
                                                  errork_399 , integralk_402) in
                             let (integralk_386:float) = integralk_402 in
                             let (errork_385:float) = errork_399 in
                             let (uk_387:float) = uk_405 in
                             let (xk_388:float) = xk_406 in
                             let _ = print_float xk_388 in
                             let _ = print_string "," in
                             let _ = print_float uk_387 in
                             let _ = print_string "," in
                             let _ = print_float errork_385 in
                             let _ = print_string "," in
                             let _ = print_float integralk_386 in
                             self.result_379 <- print_newline ())))))
                    | _ -> self.result_379 <- ()  end) ; self.result_379)) in
       cstate_422.horizon <- min cstate_422.horizon  self.h_384 ; result_427)):
    unit) in 
  let main_reset self  =
    ((self.i_382 <- true ; self.i_413 <- true ; self.integralk1_403 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
