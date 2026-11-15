(* The Zelus compiler, version 2.2-dev
  (2026-07-17-15:59) *)
open Ztypes
let setpoint = 1.

let m = 4.

let k = 15.

let b = 4.

let kp = 80.

let ki = 20.

let kd = 25.

let u_max = 40.

let u_min = (-40.)

let dt = 0.1

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
  let saturate_umax_step self ((u_334:float): float) =
    (((if (>) u_334  u_max then u_max else u_334)):float) in
  Node { alloc = saturate_umax_alloc; reset = saturate_umax_reset ;
                                      step = saturate_umax_step }
type ('b , 'a) _saturate_u =
  { mutable i_543 : 'b ; mutable i_542 : 'a }

let saturate_u  = 
  let Node { alloc = i_543_alloc; step = i_543_step ; reset = i_543_reset } = saturate_umax 
   in 
  let Node { alloc = i_542_alloc; step = i_542_step ; reset = i_542_reset } = saturate_umax 
   in
  let saturate_u_alloc _ =
    ();
    { i_543 = i_543_alloc () (* discrete *)  ;
      i_542 = i_542_alloc () (* discrete *)  } in
  let saturate_u_reset self  =
    ((i_543_reset self.i_543  ; i_542_reset self.i_542 ):unit) in 
  let saturate_u_step self ((u_335:float): float) =
    ((let (next_336:float) = i_543_step self.i_543 u_335 in
      if (<) (i_542_step self.i_542 u_335)  u_min then u_min else next_336):
    float) in
  Node { alloc = saturate_u_alloc; reset = saturate_u_reset ;
                                   step = saturate_u_step }
type ('c , 'b , 'a) _noise =
  { mutable major_338 : 'c ; mutable v_340 : 'b ; mutable n_339 : 'a }

let noise (cstate_556:Ztypes.cstate) = 
  
  let noise_alloc _ =
    cstate_556.cmax <- (+) cstate_556.cmax  2;
    { major_338 = false ;
      v_340 = { pos = 42.; der = 0. } ; n_339 = { pos = 42.; der = 0. } } in
  let noise_step self ((time_337:float) , ()) =
    ((let (cindex_557:int) = cstate_556.cindex in
      let cpos_559 = ref (cindex_557:int) in
      cstate_556.cindex <- (+) cstate_556.cindex  2 ;
      self.major_338 <- cstate_556.major ;
      (if cstate_556.major then
       for i_1 = cindex_557 to 1 do Zls.set cstate_556.dvec  i_1  0. done
       else ((self.v_340.pos <- Zls.get cstate_556.cvec  !cpos_559 ;
              cpos_559 := (+) !cpos_559  1) ;
             (self.n_339.pos <- Zls.get cstate_556.cvec  !cpos_559 ;
              cpos_559 := (+) !cpos_559  1))) ;
      (let (result_561:float) =
           self.v_340.der <- ( *. ) ((~-.) 25.)  self.n_339.pos ;
           self.n_339.der <- self.v_340.pos ; self.n_339.pos in
       cpos_559 := cindex_557 ;
       (if cstate_556.major then
        (((Zls.set cstate_556.cvec  !cpos_559  self.v_340.pos ;
           cpos_559 := (+) !cpos_559  1) ;
          (Zls.set cstate_556.cvec  !cpos_559  self.n_339.pos ;
           cpos_559 := (+) !cpos_559  1)))
        else (((Zls.set cstate_556.dvec  !cpos_559  self.v_340.der ;
                cpos_559 := (+) !cpos_559  1) ;
               (Zls.set cstate_556.dvec  !cpos_559  self.n_339.der ;
                cpos_559 := (+) !cpos_559  1)))) ; result_561)):float) in 
  let noise_reset self  =
    ((self.n_339.pos <- 0.05 ; self.v_340.pos <- 0.):unit) in
  Node { alloc = noise_alloc; step = noise_step ; reset = noise_reset }
type ('c , 'b , 'a) _sys =
  { mutable major_343 : 'c ; mutable x_345 : 'b ; mutable v_344 : 'a }

let sys (cstate_562:Ztypes.cstate) = 
  
  let sys_alloc _ =
    cstate_562.cmax <- (+) cstate_562.cmax  2;
    { major_343 = false ;
      x_345 = { pos = 42.; der = 0. } ; v_344 = { pos = 42.; der = 0. } } in
  let sys_step self ((time_342:float) , ((u_341:float): float)) =
    ((let (cindex_563:int) = cstate_562.cindex in
      let cpos_565 = ref (cindex_563:int) in
      cstate_562.cindex <- (+) cstate_562.cindex  2 ;
      self.major_343 <- cstate_562.major ;
      (if cstate_562.major then
       for i_1 = cindex_563 to 1 do Zls.set cstate_562.dvec  i_1  0. done
       else ((self.x_345.pos <- Zls.get cstate_562.cvec  !cpos_565 ;
              cpos_565 := (+) !cpos_565  1) ;
             (self.v_344.pos <- Zls.get cstate_562.cvec  !cpos_565 ;
              cpos_565 := (+) !cpos_565  1))) ;
      (let (result_567:(float  * float)) =
           self.v_344.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                      self.x_345.pos) 
                                              (( *. ) b  self.v_344.pos)) 
                                        u_341)  m ;
           self.x_345.der <- self.v_344.pos ;
           (self.x_345.pos , self.v_344.pos) in
       cpos_565 := cindex_563 ;
       (if cstate_562.major then
        (((Zls.set cstate_562.cvec  !cpos_565  self.x_345.pos ;
           cpos_565 := (+) !cpos_565  1) ;
          (Zls.set cstate_562.cvec  !cpos_565  self.v_344.pos ;
           cpos_565 := (+) !cpos_565  1)))
        else (((Zls.set cstate_562.dvec  !cpos_565  self.x_345.der ;
                cpos_565 := (+) !cpos_565  1) ;
               (Zls.set cstate_562.dvec  !cpos_565  self.v_344.der ;
                cpos_565 := (+) !cpos_565  1)))) ; result_567)):float * float) in
  
  let sys_reset self  =
    ((self.v_344.pos <- 0. ; self.x_345.pos <- 0.):unit) in
  Node { alloc = sys_alloc; step = sys_step ; reset = sys_reset }
type ('b , 'a) _pid =
  { mutable i_544 : 'b ; mutable integral_antiwindup_349 : 'a }

let pid  = 
  let Node { alloc = i_544_alloc; step = i_544_step ; reset = i_544_reset } = saturate_u 
   in
  let pid_alloc _ =
    ();
    { integral_antiwindup_349 = (42.:float);
      i_544 = i_544_alloc () (* discrete *)  } in
  let pid_reset self  =
    ((self.integral_antiwindup_349 <- 0. ; i_544_reset self.i_544 ):unit) in 
  let pid_step self (((x_347:float): float) , ((v_346:float): float)) =
    ((let ((error_348:float): float) = (-.) setpoint  x_347 in
      let (l_352:float) = self.integral_antiwindup_349 in
      let ((u_350:float): float) =
          (-.) ((+.) (( *. ) kp  error_348)  (( *. ) ki  l_352)) 
               (( *. ) kd  v_346) in
      let ((copy_538:float): float) =
          if (||) ((&&) ((>) u_350  u_max)  ((>) error_348  0.)) 
                  ((&&) ((<) u_350  u_min)  ((<) error_348  0.))
          then l_352
          else (+.) l_352  (( *. ) dt  error_348) in
      self.integral_antiwindup_349 <- copy_538 ;
      (let (u_sat_351:float) = i_544_step self.i_544 u_350 in
       (error_348 , u_sat_351))):float * float) in
  Node { alloc = pid_alloc; reset = pid_reset ; step = pid_step }
type ('b , 'a) _pid_esin =
  { mutable i_545 : 'b ; mutable integral_antiwindup_357 : 'a }

let pid_esin  = 
  let Node { alloc = i_545_alloc; step = i_545_step ; reset = i_545_reset } = saturate_u 
   in
  let pid_esin_alloc _ =
    ();
    { integral_antiwindup_357 = (42.:float);
      i_545 = i_545_alloc () (* discrete *)  } in
  let pid_esin_reset self  =
    ((self.integral_antiwindup_357 <- 0. ; i_545_reset self.i_545 ):unit) in 
  let pid_esin_step self (((x_355:float): float) ,
                          ((v_354:float): float) , ((noise_353:float): float)) =
    ((let ((error_356:float): float) = (-.) setpoint  ((+.) x_355  noise_353) in
      let (l_360:float) = self.integral_antiwindup_357 in
      let ((u_358:float): float) =
          (-.) ((+.) (( *. ) kp  error_356)  (( *. ) ki  l_360)) 
               (( *. ) kd  ((+.) v_354  0.)) in
      let ((copy_539:float): float) =
          if (||) ((&&) ((>) u_358  u_max)  ((>) error_356  0.)) 
                  ((&&) ((<) u_358  u_min)  ((<) error_356  0.))
          then l_360
          else (+.) l_360  (( *. ) dt  error_356) in
      self.integral_antiwindup_357 <- copy_539 ;
      (let (u_sat_359:float) = i_545_step self.i_545 u_358 in
       (error_356 , u_sat_359))):float * float) in
  Node { alloc = pid_esin_alloc; reset = pid_esin_reset ;
                                 step = pid_esin_step }
type ('b , 'a) _pid_estat =
  { mutable i_546 : 'b ; mutable integral_antiwindup_364 : 'a }

let pid_estat  = 
  let Node { alloc = i_546_alloc; step = i_546_step ; reset = i_546_reset } = saturate_u 
   in
  let pid_estat_alloc _ =
    ();
    { integral_antiwindup_364 = (42.:float);
      i_546 = i_546_alloc () (* discrete *)  } in
  let pid_estat_reset self  =
    ((self.integral_antiwindup_364 <- 0. ; i_546_reset self.i_546 ):unit) in 
  let pid_estat_step self (((x_362:float): float) , ((v_361:float): float)) =
    ((let ((error_363:float): float) = (-.) setpoint  ((-.) x_362  0.5) in
      let (l_367:float) = self.integral_antiwindup_364 in
      let ((u_365:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_363)  (( *. ) ki  l_367)) 
                     (( *. ) kd  ((+.) v_361  0.)))  0. in
      let ((copy_540:float): float) =
          if (||) ((&&) ((>) u_365  u_max)  ((>) error_363  0.)) 
                  ((&&) ((<) u_365  u_min)  ((<) error_363  0.))
          then l_367
          else (+.) l_367  (( *. ) dt  error_363) in
      self.integral_antiwindup_364 <- copy_540 ;
      (let (u_sat_366:float) = i_546_step self.i_546 u_365 in
       (error_363 , u_sat_366))):float * float) in
  Node { alloc = pid_estat_alloc; reset = pid_estat_reset ;
                                  step = pid_estat_step }
type ('b , 'a) _pid_e =
  { mutable i_547 : 'b ; mutable integral_antiwindup_372 : 'a }

let pid_e  = 
  let Node { alloc = i_547_alloc; step = i_547_step ; reset = i_547_reset } = saturate_u 
   in
  let pid_e_alloc _ =
    ();
    { integral_antiwindup_372 = (42.:float);
      i_547 = i_547_alloc () (* discrete *)  } in
  let pid_e_reset self  =
    ((self.integral_antiwindup_372 <- 0. ; i_547_reset self.i_547 ):unit) in 
  let pid_e_step self (((x_370:float): float) ,
                       ((v_369:float): float) , ((noise_368:float): float)) =
    ((let ((error_371:float): float) =
          (-.) setpoint  ((-.) ((+.) x_370  noise_368)  0.5) in
      let (l_375:float) = self.integral_antiwindup_372 in
      let ((u_373:float): float) =
          (+.) ((-.) ((+.) (( *. ) kp  error_371)  (( *. ) ki  l_375)) 
                     (( *. ) kd  ((+.) v_369  0.)))  noise_368 in
      let ((copy_541:float): float) =
          if (||) ((&&) ((>) u_373  u_max)  ((>) error_371  0.)) 
                  ((&&) ((<) u_373  u_min)  ((<) error_371  0.))
          then l_375
          else (+.) l_375  (( *. ) dt  error_371) in
      self.integral_antiwindup_372 <- copy_541 ;
      (let (u_sat_374:float) = i_547_step self.i_547 u_373 in
       (error_371 , u_sat_374))):float * float) in
  Node { alloc = pid_e_alloc; reset = pid_e_reset ; step = pid_e_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_548 : 'i ;
    mutable major_377 : 'h ;
    mutable h_395 : 'g ;
    mutable h_393 : 'f ;
    mutable i_391 : 'e ;
    mutable h_389 : 'd ;
    mutable x_386 : 'c ; mutable v_385 : 'b ; mutable result_383 : 'a }

let exec (cstate_568:Ztypes.cstate) = 
  let Node { alloc = i_548_alloc; step = i_548_step ; reset = i_548_reset } = pid 
   in
  let exec_alloc _ =
    cstate_568.cmax <- (+) cstate_568.cmax  2;
    { major_377 = false ;
      h_395 = 42. ;
      h_393 = (42.:float) ;
      i_391 = (false:bool) ;
      h_389 = (42.:float) ;
      x_386 = { pos = 42.; der = 0. } ;
      v_385 = { pos = 42.; der = 0. } ;
      result_383 = ((42. , 42.):float * float);
      i_548 = i_548_alloc () (* discrete *)  } in
  let exec_step self ((time_376:float) , ()) =
    ((let (cindex_569:int) = cstate_568.cindex in
      let cpos_571 = ref (cindex_569:int) in
      cstate_568.cindex <- (+) cstate_568.cindex  2 ;
      self.major_377 <- cstate_568.major ;
      (if cstate_568.major then
       for i_1 = cindex_569 to 1 do Zls.set cstate_568.dvec  i_1  0. done
       else ((self.x_386.pos <- Zls.get cstate_568.cvec  !cpos_571 ;
              cpos_571 := (+) !cpos_571  1) ;
             (self.v_385.pos <- Zls.get cstate_568.cvec  !cpos_571 ;
              cpos_571 := (+) !cpos_571  1))) ;
      (let (result_573:(float  * float  * float  * float)) =
           let h_394 = ref (infinity:float) in
           let encore_392 = ref (false:bool) in
           let (x_382:float) = self.x_386.pos in
           let (v_381:float) = self.v_385.pos in
           let ((l_387:float) , (l_388:float)) = self.result_383 in
           (if self.i_391 then self.h_389 <- (+.) time_376  0.) ;
           (let (z_390:bool) =
                (&&) self.major_377  ((>=) time_376  self.h_389) in
            let (trigger_379:zero) = z_390 in
            (begin match trigger_379 with
                   | true ->
                       encore_392 := true ;
                       self.result_383 <- i_548_step self.i_548
                                            (x_382 , v_381) | _ -> ()  end) ;
            self.h_393 <- (if !encore_392 then 0. else infinity) ;
            self.h_389 <- (if z_390 then (+.) self.h_389  dt else self.h_389)
            ;
            h_394 := min !h_394  (min self.h_393  self.h_389) ;
            self.h_395 <- !h_394 ;
            self.i_391 <- false ;
            (let ((error_378:float) , (u_380:float)) = self.result_383 in
             let ((u_384:float): float) = u_380 in
             self.v_385.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                        self.x_386.pos) 
                                                (( *. ) b  self.v_385.pos)) 
                                          u_384)  m ;
             self.x_386.der <- self.v_385.pos ;
             (x_382 , v_381 , error_378 , u_380))) in
       cstate_568.horizon <- min cstate_568.horizon  self.h_395 ;
       cpos_571 := cindex_569 ;
       (if cstate_568.major then
        (((Zls.set cstate_568.cvec  !cpos_571  self.x_386.pos ;
           cpos_571 := (+) !cpos_571  1) ;
          (Zls.set cstate_568.cvec  !cpos_571  self.v_385.pos ;
           cpos_571 := (+) !cpos_571  1)))
        else (((Zls.set cstate_568.dvec  !cpos_571  self.x_386.der ;
                cpos_571 := (+) !cpos_571  1) ;
               (Zls.set cstate_568.dvec  !cpos_571  self.v_385.der ;
                cpos_571 := (+) !cpos_571  1)))) ; result_573)):float *
                                                                float *
                                                                float * float) in
  
  let exec_reset self  =
    ((self.x_386.pos <- 0. ;
      self.v_385.pos <- 0. ;
      self.result_383 <- (0. , 0.) ;
      self.i_391 <- true ; i_548_reset self.i_548 ):unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec_esin =
  { mutable i_549 : 'k ;
    mutable major_397 : 'j ;
    mutable h_418 : 'i ;
    mutable h_416 : 'h ;
    mutable i_414 : 'g ;
    mutable h_412 : 'f ;
    mutable x_409 : 'e ;
    mutable v_408 : 'd ;
    mutable result_406 : 'c ; mutable v_405 : 'b ; mutable n_404 : 'a }

let exec_esin (cstate_574:Ztypes.cstate) = 
  let Node { alloc = i_549_alloc; step = i_549_step ; reset = i_549_reset } = pid_esin 
   in
  let exec_esin_alloc _ =
    cstate_574.cmax <- (+) cstate_574.cmax  4;
    { major_397 = false ;
      h_418 = 42. ;
      h_416 = (42.:float) ;
      i_414 = (false:bool) ;
      h_412 = (42.:float) ;
      x_409 = { pos = 42.; der = 0. } ;
      v_408 = { pos = 42.; der = 0. } ;
      result_406 = ((42. , 42.):float * float) ;
      v_405 = { pos = 42.; der = 0. } ; n_404 = { pos = 42.; der = 0. };
      i_549 = i_549_alloc () (* discrete *)  } in
  let exec_esin_step self ((time_396:float) , ()) =
    ((let (cindex_575:int) = cstate_574.cindex in
      let cpos_577 = ref (cindex_575:int) in
      cstate_574.cindex <- (+) cstate_574.cindex  4 ;
      self.major_397 <- cstate_574.major ;
      (if cstate_574.major then
       for i_1 = cindex_575 to 3 do Zls.set cstate_574.dvec  i_1  0. done
       else ((self.x_409.pos <- Zls.get cstate_574.cvec  !cpos_577 ;
              cpos_577 := (+) !cpos_577  1) ;
             (self.v_408.pos <- Zls.get cstate_574.cvec  !cpos_577 ;
              cpos_577 := (+) !cpos_577  1) ;
             (self.v_405.pos <- Zls.get cstate_574.cvec  !cpos_577 ;
              cpos_577 := (+) !cpos_577  1) ;
             (self.n_404.pos <- Zls.get cstate_574.cvec  !cpos_577 ;
              cpos_577 := (+) !cpos_577  1))) ;
      (let (result_579:(float  * float  * float  * float  * float)) =
           let h_417 = ref (infinity:float) in
           let encore_415 = ref (false:bool) in
           let (x_403:float) = self.x_409.pos in
           let (v_402:float) = self.v_408.pos in
           let ((l_410:float) , (l_411:float)) = self.result_406 in
           let (n_399:float) = self.n_404.pos in
           (if self.i_414 then self.h_412 <- (+.) time_396  0.) ;
           (let (z_413:bool) =
                (&&) self.major_397  ((>=) time_396  self.h_412) in
            let (trigger_400:zero) = z_413 in
            (begin match trigger_400 with
                   | true ->
                       encore_415 := true ;
                       self.result_406 <- i_549_step self.i_549
                                            (x_403 , v_402 , n_399)
                   | _ -> ()  end) ;
            self.h_416 <- (if !encore_415 then 0. else infinity) ;
            self.h_412 <- (if z_413 then (+.) self.h_412  dt else self.h_412)
            ;
            h_417 := min !h_417  (min self.h_416  self.h_412) ;
            self.h_418 <- !h_417 ;
            self.i_414 <- false ;
            (let ((error_398:float) , (u_401:float)) = self.result_406 in
             let ((u_407:float): float) = u_401 in
             self.v_408.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                        self.x_409.pos) 
                                                (( *. ) b  self.v_408.pos)) 
                                          u_407)  m ;
             self.x_409.der <- self.v_408.pos ;
             (let () = () in
              self.v_405.der <- ( *. ) ((~-.) 25.)  self.n_404.pos ;
              self.n_404.der <- self.v_405.pos ;
              (x_403 , v_402 , error_398 , u_401 , n_399)))) in
       cstate_574.horizon <- min cstate_574.horizon  self.h_418 ;
       cpos_577 := cindex_575 ;
       (if cstate_574.major then
        (((Zls.set cstate_574.cvec  !cpos_577  self.x_409.pos ;
           cpos_577 := (+) !cpos_577  1) ;
          (Zls.set cstate_574.cvec  !cpos_577  self.v_408.pos ;
           cpos_577 := (+) !cpos_577  1) ;
          (Zls.set cstate_574.cvec  !cpos_577  self.v_405.pos ;
           cpos_577 := (+) !cpos_577  1) ;
          (Zls.set cstate_574.cvec  !cpos_577  self.n_404.pos ;
           cpos_577 := (+) !cpos_577  1)))
        else (((Zls.set cstate_574.dvec  !cpos_577  self.x_409.der ;
                cpos_577 := (+) !cpos_577  1) ;
               (Zls.set cstate_574.dvec  !cpos_577  self.v_408.der ;
                cpos_577 := (+) !cpos_577  1) ;
               (Zls.set cstate_574.dvec  !cpos_577  self.v_405.der ;
                cpos_577 := (+) !cpos_577  1) ;
               (Zls.set cstate_574.dvec  !cpos_577  self.n_404.der ;
                cpos_577 := (+) !cpos_577  1)))) ; result_579)):float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_esin_reset self  =
    ((self.x_409.pos <- 0. ;
      self.v_408.pos <- 0. ;
      self.result_406 <- (0. , 0.) ;
      self.n_404.pos <- 0.05 ;
      self.i_414 <- true ; i_549_reset self.i_549  ; self.v_405.pos <- 0.):
    unit) in
  Node { alloc = exec_esin_alloc; step = exec_esin_step ;
                                  reset = exec_esin_reset }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec_estat =
  { mutable i_550 : 'i ;
    mutable major_420 : 'h ;
    mutable h_438 : 'g ;
    mutable h_436 : 'f ;
    mutable i_434 : 'e ;
    mutable h_432 : 'd ;
    mutable x_429 : 'c ; mutable v_428 : 'b ; mutable result_426 : 'a }

let exec_estat (cstate_580:Ztypes.cstate) = 
  let Node { alloc = i_550_alloc; step = i_550_step ; reset = i_550_reset } = pid_estat 
   in
  let exec_estat_alloc _ =
    cstate_580.cmax <- (+) cstate_580.cmax  2;
    { major_420 = false ;
      h_438 = 42. ;
      h_436 = (42.:float) ;
      i_434 = (false:bool) ;
      h_432 = (42.:float) ;
      x_429 = { pos = 42.; der = 0. } ;
      v_428 = { pos = 42.; der = 0. } ;
      result_426 = ((42. , 42.):float * float);
      i_550 = i_550_alloc () (* discrete *)  } in
  let exec_estat_step self ((time_419:float) , ()) =
    ((let (cindex_581:int) = cstate_580.cindex in
      let cpos_583 = ref (cindex_581:int) in
      cstate_580.cindex <- (+) cstate_580.cindex  2 ;
      self.major_420 <- cstate_580.major ;
      (if cstate_580.major then
       for i_1 = cindex_581 to 1 do Zls.set cstate_580.dvec  i_1  0. done
       else ((self.x_429.pos <- Zls.get cstate_580.cvec  !cpos_583 ;
              cpos_583 := (+) !cpos_583  1) ;
             (self.v_428.pos <- Zls.get cstate_580.cvec  !cpos_583 ;
              cpos_583 := (+) !cpos_583  1))) ;
      (let (result_585:(float  * float  * float  * float)) =
           let h_437 = ref (infinity:float) in
           let encore_435 = ref (false:bool) in
           let (x_425:float) = self.x_429.pos in
           let (v_424:float) = self.v_428.pos in
           let ((l_430:float) , (l_431:float)) = self.result_426 in
           (if self.i_434 then self.h_432 <- (+.) time_419  0.) ;
           (let (z_433:bool) =
                (&&) self.major_420  ((>=) time_419  self.h_432) in
            let (trigger_422:zero) = z_433 in
            (begin match trigger_422 with
                   | true ->
                       encore_435 := true ;
                       self.result_426 <- i_550_step self.i_550
                                            (x_425 , v_424) | _ -> ()  end) ;
            self.h_436 <- (if !encore_435 then 0. else infinity) ;
            self.h_432 <- (if z_433 then (+.) self.h_432  dt else self.h_432)
            ;
            h_437 := min !h_437  (min self.h_436  self.h_432) ;
            self.h_438 <- !h_437 ;
            self.i_434 <- false ;
            (let ((error_421:float) , (u_423:float)) = self.result_426 in
             let ((u_427:float): float) = u_423 in
             self.v_428.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                        self.x_429.pos) 
                                                (( *. ) b  self.v_428.pos)) 
                                          u_427)  m ;
             self.x_429.der <- self.v_428.pos ;
             (x_425 , v_424 , error_421 , u_423))) in
       cstate_580.horizon <- min cstate_580.horizon  self.h_438 ;
       cpos_583 := cindex_581 ;
       (if cstate_580.major then
        (((Zls.set cstate_580.cvec  !cpos_583  self.x_429.pos ;
           cpos_583 := (+) !cpos_583  1) ;
          (Zls.set cstate_580.cvec  !cpos_583  self.v_428.pos ;
           cpos_583 := (+) !cpos_583  1)))
        else (((Zls.set cstate_580.dvec  !cpos_583  self.x_429.der ;
                cpos_583 := (+) !cpos_583  1) ;
               (Zls.set cstate_580.dvec  !cpos_583  self.v_428.der ;
                cpos_583 := (+) !cpos_583  1)))) ; result_585)):float *
                                                                float *
                                                                float * float) in
  
  let exec_estat_reset self  =
    ((self.x_429.pos <- 0. ;
      self.v_428.pos <- 0. ;
      self.result_426 <- (0. , 0.) ;
      self.i_434 <- true ; i_550_reset self.i_550 ):unit) in
  Node { alloc = exec_estat_alloc; step = exec_estat_step ;
                                   reset = exec_estat_reset }
type ('k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec_e =
  { mutable i_551 : 'k ;
    mutable major_440 : 'j ;
    mutable h_461 : 'i ;
    mutable h_459 : 'h ;
    mutable i_457 : 'g ;
    mutable h_455 : 'f ;
    mutable x_452 : 'e ;
    mutable v_451 : 'd ;
    mutable result_449 : 'c ; mutable v_448 : 'b ; mutable n_447 : 'a }

let exec_e (cstate_586:Ztypes.cstate) = 
  let Node { alloc = i_551_alloc; step = i_551_step ; reset = i_551_reset } = pid_e 
   in
  let exec_e_alloc _ =
    cstate_586.cmax <- (+) cstate_586.cmax  4;
    { major_440 = false ;
      h_461 = 42. ;
      h_459 = (42.:float) ;
      i_457 = (false:bool) ;
      h_455 = (42.:float) ;
      x_452 = { pos = 42.; der = 0. } ;
      v_451 = { pos = 42.; der = 0. } ;
      result_449 = ((42. , 42.):float * float) ;
      v_448 = { pos = 42.; der = 0. } ; n_447 = { pos = 42.; der = 0. };
      i_551 = i_551_alloc () (* discrete *)  } in
  let exec_e_step self ((time_439:float) , ()) =
    ((let (cindex_587:int) = cstate_586.cindex in
      let cpos_589 = ref (cindex_587:int) in
      cstate_586.cindex <- (+) cstate_586.cindex  4 ;
      self.major_440 <- cstate_586.major ;
      (if cstate_586.major then
       for i_1 = cindex_587 to 3 do Zls.set cstate_586.dvec  i_1  0. done
       else ((self.x_452.pos <- Zls.get cstate_586.cvec  !cpos_589 ;
              cpos_589 := (+) !cpos_589  1) ;
             (self.v_451.pos <- Zls.get cstate_586.cvec  !cpos_589 ;
              cpos_589 := (+) !cpos_589  1) ;
             (self.v_448.pos <- Zls.get cstate_586.cvec  !cpos_589 ;
              cpos_589 := (+) !cpos_589  1) ;
             (self.n_447.pos <- Zls.get cstate_586.cvec  !cpos_589 ;
              cpos_589 := (+) !cpos_589  1))) ;
      (let (result_591:(float  * float  * float  * float)) =
           let h_460 = ref (infinity:float) in
           let encore_458 = ref (false:bool) in
           let (x_446:float) = self.x_452.pos in
           let (v_445:float) = self.v_451.pos in
           let ((l_453:float) , (l_454:float)) = self.result_449 in
           let (n_442:float) = self.n_447.pos in
           (if self.i_457 then self.h_455 <- (+.) time_439  0.) ;
           (let (z_456:bool) =
                (&&) self.major_440  ((>=) time_439  self.h_455) in
            let (trigger_443:zero) = z_456 in
            (begin match trigger_443 with
                   | true ->
                       encore_458 := true ;
                       self.result_449 <- i_551_step self.i_551
                                            (x_446 , v_445 , n_442)
                   | _ -> ()  end) ;
            self.h_459 <- (if !encore_458 then 0. else infinity) ;
            self.h_455 <- (if z_456 then (+.) self.h_455  dt else self.h_455)
            ;
            h_460 := min !h_460  (min self.h_459  self.h_455) ;
            self.h_461 <- !h_460 ;
            self.i_457 <- false ;
            (let ((error_441:float) , (u_444:float)) = self.result_449 in
             let ((u_450:float): float) = u_444 in
             self.v_451.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                        self.x_452.pos) 
                                                (( *. ) b  self.v_451.pos)) 
                                          u_450)  m ;
             self.x_452.der <- self.v_451.pos ;
             (let () = () in
              self.v_448.der <- ( *. ) ((~-.) 25.)  self.n_447.pos ;
              self.n_447.der <- self.v_448.pos ;
              (x_446 , v_445 , error_441 , u_444)))) in
       cstate_586.horizon <- min cstate_586.horizon  self.h_461 ;
       cpos_589 := cindex_587 ;
       (if cstate_586.major then
        (((Zls.set cstate_586.cvec  !cpos_589  self.x_452.pos ;
           cpos_589 := (+) !cpos_589  1) ;
          (Zls.set cstate_586.cvec  !cpos_589  self.v_451.pos ;
           cpos_589 := (+) !cpos_589  1) ;
          (Zls.set cstate_586.cvec  !cpos_589  self.v_448.pos ;
           cpos_589 := (+) !cpos_589  1) ;
          (Zls.set cstate_586.cvec  !cpos_589  self.n_447.pos ;
           cpos_589 := (+) !cpos_589  1)))
        else (((Zls.set cstate_586.dvec  !cpos_589  self.x_452.der ;
                cpos_589 := (+) !cpos_589  1) ;
               (Zls.set cstate_586.dvec  !cpos_589  self.v_451.der ;
                cpos_589 := (+) !cpos_589  1) ;
               (Zls.set cstate_586.dvec  !cpos_589  self.v_448.der ;
                cpos_589 := (+) !cpos_589  1) ;
               (Zls.set cstate_586.dvec  !cpos_589  self.n_447.der ;
                cpos_589 := (+) !cpos_589  1)))) ; result_591)):float *
                                                                float *
                                                                float * float) in
  
  let exec_e_reset self  =
    ((self.x_452.pos <- 0. ;
      self.v_451.pos <- 0. ;
      self.result_449 <- (0. , 0.) ;
      self.n_447.pos <- 0.05 ;
      self.i_457 <- true ; i_551_reset self.i_551  ; self.v_448.pos <- 0.):
    unit) in
  Node { alloc = exec_e_alloc; step = exec_e_step ; reset = exec_e_reset }
type ('d1 ,
      'c1 ,
      'b1 ,
      'a1 ,
      'z ,
      'y ,
      'x ,
      'w ,
      'v ,
      'u ,
      't ,
      's ,
      'r ,
      'q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_555 : 'd1 ;
    mutable i_554 : 'c1 ;
    mutable i_553 : 'b1 ;
    mutable i_552 : 'a1 ;
    mutable major_463 : 'z ;
    mutable h_537 : 'y ;
    mutable h_535 : 'x ;
    mutable i_533 : 'w ;
    mutable h_531 : 'v ;
    mutable h_529 : 'u ;
    mutable h_527 : 't ;
    mutable h_525 : 's ;
    mutable h_523 : 'r ;
    mutable result_514 : 'q ;
    mutable x_513 : 'p ;
    mutable v_512 : 'o ;
    mutable result_510 : 'n ;
    mutable v_509 : 'm ;
    mutable n_508 : 'l ;
    mutable x_501 : 'k ;
    mutable v_500 : 'j ;
    mutable result_498 : 'i ;
    mutable x_492 : 'h ;
    mutable v_491 : 'g ;
    mutable result_489 : 'f ;
    mutable v_488 : 'e ;
    mutable n_487 : 'd ;
    mutable x_480 : 'c ; mutable v_479 : 'b ; mutable result_477 : 'a }

let main (cstate_592:Ztypes.cstate) = 
  let Node { alloc = i_555_alloc; step = i_555_step ; reset = i_555_reset } = pid_e 
   in 
  let Node { alloc = i_554_alloc; step = i_554_step ; reset = i_554_reset } = pid_estat 
   in 
  let Node { alloc = i_553_alloc; step = i_553_step ; reset = i_553_reset } = pid_esin 
   in 
  let Node { alloc = i_552_alloc; step = i_552_step ; reset = i_552_reset } = pid 
   in
  let main_alloc _ =
    cstate_592.cmax <- (+) cstate_592.cmax  12;
    { major_463 = false ;
      h_537 = 42. ;
      h_535 = (42.:float) ;
      i_533 = (false:bool) ;
      h_531 = (42.:float) ;
      h_529 = (42.:float) ;
      h_527 = (42.:float) ;
      h_525 = (42.:float) ;
      h_523 = (42.:float) ;
      result_514 = (():unit) ;
      x_513 = { pos = 42.; der = 0. } ;
      v_512 = { pos = 42.; der = 0. } ;
      result_510 = ((42. , 42.):float * float) ;
      v_509 = { pos = 42.; der = 0. } ;
      n_508 = { pos = 42.; der = 0. } ;
      x_501 = { pos = 42.; der = 0. } ;
      v_500 = { pos = 42.; der = 0. } ;
      result_498 = ((42. , 42.):float * float) ;
      x_492 = { pos = 42.; der = 0. } ;
      v_491 = { pos = 42.; der = 0. } ;
      result_489 = ((42. , 42.):float * float) ;
      v_488 = { pos = 42.; der = 0. } ;
      n_487 = { pos = 42.; der = 0. } ;
      x_480 = { pos = 42.; der = 0. } ;
      v_479 = { pos = 42.; der = 0. } ;
      result_477 = ((42. , 42.):float * float);
      i_555 = i_555_alloc () (* discrete *)  ;
      i_554 = i_554_alloc () (* discrete *)  ;
      i_553 = i_553_alloc () (* discrete *)  ;
      i_552 = i_552_alloc () (* discrete *)  } in
  let main_step self ((time_462:float) , ()) =
    ((let (cindex_593:int) = cstate_592.cindex in
      let cpos_595 = ref (cindex_593:int) in
      cstate_592.cindex <- (+) cstate_592.cindex  12 ;
      self.major_463 <- cstate_592.major ;
      (if cstate_592.major then
       for i_1 = cindex_593 to 11 do Zls.set cstate_592.dvec  i_1  0. done
       else ((self.x_513.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_512.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_509.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.n_508.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.x_501.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_500.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.x_492.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_491.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_488.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.n_487.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.x_480.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1) ;
             (self.v_479.pos <- Zls.get cstate_592.cvec  !cpos_595 ;
              cpos_595 := (+) !cpos_595  1))) ;
      (let (result_597:unit) =
           let h_536 = ref (infinity:float) in
           let encore_534 = ref (false:bool) in
           let (x_507:float) = self.x_513.pos in
           let (v_506:float) = self.v_512.pos in
           let ((l_521:float) , (l_522:float)) = self.result_510 in
           let (n_503:float) = self.n_508.pos in
           (if self.i_533 then self.h_531 <- (+.) time_462  0.) ;
           (let (z_532:bool) =
                (&&) self.major_463  ((>=) time_462  self.h_531) in
            let (trigger_504:zero) = z_532 in
            (begin match trigger_504 with
                   | true ->
                       encore_534 := true ;
                       self.result_510 <- i_555_step self.i_555
                                            (x_507 , v_506 , n_503)
                   | _ -> ()  end) ;
            (let (x_497:float) = self.x_501.pos in
             let (v_496:float) = self.v_500.pos in
             let ((l_519:float) , (l_520:float)) = self.result_498 in
             (if self.i_533 then self.h_529 <- (+.) time_462  0.) ;
             (let (z_530:bool) =
                  (&&) self.major_463  ((>=) time_462  self.h_529) in
              let (trigger_494:zero) = z_530 in
              (begin match trigger_494 with
                     | true ->
                         encore_534 := true ;
                         self.result_498 <- i_554_step self.i_554
                                              (x_497 , v_496) | _ -> ()  end)
              ;
              (let (x_486:float) = self.x_492.pos in
               let (v_485:float) = self.v_491.pos in
               let ((l_517:float) , (l_518:float)) = self.result_489 in
               let (n_482:float) = self.n_487.pos in
               (if self.i_533 then self.h_527 <- (+.) time_462  0.) ;
               (let (z_528:bool) =
                    (&&) self.major_463  ((>=) time_462  self.h_527) in
                let (trigger_483:zero) = z_528 in
                (begin match trigger_483 with
                       | true ->
                           encore_534 := true ;
                           self.result_489 <- i_553_step self.i_553
                                                (x_486 , v_485 , n_482)
                       | _ -> ()  end) ;
                (let (x_476:float) = self.x_480.pos in
                 let (v_475:float) = self.v_479.pos in
                 let ((l_515:float) , (l_516:float)) = self.result_477 in
                 (if self.i_533 then self.h_525 <- (+.) time_462  0.) ;
                 (let (z_526:bool) =
                      (&&) self.major_463  ((>=) time_462  self.h_525) in
                  let (trigger_473:zero) = z_526 in
                  (begin match trigger_473 with
                         | true ->
                             encore_534 := true ;
                             self.result_477 <- i_552_step self.i_552
                                                  (x_476 , v_475) | _ -> ()  end)
                  ;
                  self.h_535 <- (if !encore_534 then 0. else infinity) ;
                  self.h_531 <- (if z_532
                                 then (+.) self.h_531  dt
                                 else self.h_531) ;
                  self.h_529 <- (if z_530
                                 then (+.) self.h_529  dt
                                 else self.h_529) ;
                  self.h_527 <- (if z_528
                                 then (+.) self.h_527  dt
                                 else self.h_527) ;
                  self.h_525 <- (if z_526
                                 then (+.) self.h_525  dt
                                 else self.h_525) ;
                  (if self.i_533 then self.h_523 <- (+.) time_462  0.) ;
                  (let (z_524:bool) =
                       (&&) self.major_463  ((>=) time_462  self.h_523) in
                   self.h_523 <- (if z_524
                                  then (+.) self.h_523  0.1
                                  else self.h_523) ;
                   h_536 := min !h_536 
                                (min (min (min (min (min self.h_535 
                                                         self.h_531) 
                                                    self.h_529)  self.h_527) 
                                          self.h_525)  self.h_523) ;
                   self.h_537 <- !h_536 ;
                   self.i_533 <- false ;
                   (let () = () in
                    let ((error_502:float) , (u_505:float)) = self.result_510 in
                    let ((u_511:float): float) = u_505 in
                    self.v_512.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                               self.x_513.pos)
                                                       
                                                       (( *. ) b 
                                                               self.v_512.pos))
                                                  u_511)  m ;
                    self.x_513.der <- self.v_512.pos ;
                    (let () = () in
                     self.v_509.der <- ( *. ) ((~-.) 25.)  self.n_508.pos ;
                     self.n_508.der <- self.v_509.pos ;
                     (let _ = v_506 in
                      let _ = error_502 in
                      let _ = u_505 in
                      let () = () in
                      let ((error_493:float) , (u_495:float)) =
                          self.result_498 in
                      let ((u_499:float): float) = u_495 in
                      self.v_500.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                                 self.x_501.pos)
                                                         
                                                         (( *. ) b 
                                                                 self.v_500.pos))
                                                    u_499)  m ;
                      self.x_501.der <- self.v_500.pos ;
                      (let _ = v_496 in
                       let _ = error_493 in
                       let _ = u_495 in
                       let () = () in
                       let ((error_481:float) , (u_484:float)) =
                           self.result_489 in
                       let ((u_490:float): float) = u_484 in
                       self.v_491.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                                  self.x_492.pos)
                                                          
                                                          (( *. ) b 
                                                                  self.v_491.pos))
                                                     u_490)  m ;
                       self.x_492.der <- self.v_491.pos ;
                       (let () = () in
                        self.v_488.der <- ( *. ) ((~-.) 25.)  self.n_487.pos
                        ;
                        self.n_487.der <- self.v_488.pos ;
                        (let _ = v_485 in
                         let _ = error_481 in
                         let _ = u_484 in
                         let () = () in
                         let ((error_472:float) , (u_474:float)) =
                             self.result_477 in
                         let ((u_478:float): float) = u_474 in
                         self.v_479.der <- (/.) ((+.) ((-.) (( *. ) (
                                                                    (~-.) k) 
                                                                    self.x_480.pos)
                                                            
                                                            (( *. ) b 
                                                                    self.v_479.pos))
                                                       u_478)  m ;
                         self.x_480.der <- self.v_479.pos ;
                         (let _ = error_472 in
                          let (x_e_469:float) = x_507 in
                          let (x_estat_471:float) = x_497 in
                          let (x_esin_470:float) = x_486 in
                          let (noise_464:float) = n_482 in
                          let (x_468:float) = x_476 in
                          let (v_467:float) = v_475 in
                          let (u_466:float) = u_474 in
                          let (trigger_465:zero) = z_524 in
                          (begin match trigger_465 with
                                 | true ->
                                     let _ = print_float x_468 in
                                     let _ = print_string ", " in
                                     let _ = print_float v_467 in
                                     let _ = print_string "," in
                                     let _ = print_float u_466 in
                                     let _ = print_string "," in
                                     let _ = print_float x_esin_470 in
                                     let _ = print_string "," in
                                     let _ = print_float noise_464 in
                                     let _ = print_string "," in
                                     let _ = print_float x_estat_471 in
                                     let _ = print_string "," in
                                     let _ = print_float x_e_469 in
                                     self.result_514 <- print_newline ()
                                 | _ -> self.result_514 <- ()  end) ;
                          self.result_514))))))))))))))) in
       cstate_592.horizon <- min cstate_592.horizon  self.h_537 ;
       cpos_595 := cindex_593 ;
       (if cstate_592.major then
        (((Zls.set cstate_592.cvec  !cpos_595  self.x_513.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_512.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_509.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.n_508.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.x_501.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_500.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.x_492.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_491.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_488.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.n_487.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.x_480.pos ;
           cpos_595 := (+) !cpos_595  1) ;
          (Zls.set cstate_592.cvec  !cpos_595  self.v_479.pos ;
           cpos_595 := (+) !cpos_595  1)))
        else (((Zls.set cstate_592.dvec  !cpos_595  self.x_513.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_512.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_509.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.n_508.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.x_501.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_500.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.x_492.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_491.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_488.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.n_487.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.x_480.der ;
                cpos_595 := (+) !cpos_595  1) ;
               (Zls.set cstate_592.dvec  !cpos_595  self.v_479.der ;
                cpos_595 := (+) !cpos_595  1)))) ; result_597)):unit) in 
  let main_reset self  =
    ((self.x_513.pos <- 0. ;
      self.v_512.pos <- 0. ;
      self.result_510 <- (0. , 0.) ;
      self.n_508.pos <- 0.05 ;
      self.i_533 <- true ;
      i_555_reset self.i_555  ;
      self.x_501.pos <- 0. ;
      self.v_500.pos <- 0. ;
      self.result_498 <- (0. , 0.) ;
      i_554_reset self.i_554  ;
      self.x_492.pos <- 0. ;
      self.v_491.pos <- 0. ;
      self.result_489 <- (0. , 0.) ;
      self.n_487.pos <- 0.05 ;
      i_553_reset self.i_553  ;
      self.x_480.pos <- 0. ;
      self.v_479.pos <- 0. ;
      self.result_477 <- (0. , 0.) ;
      i_552_reset self.i_552  ; self.v_509.pos <- 0. ; self.v_488.pos <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
