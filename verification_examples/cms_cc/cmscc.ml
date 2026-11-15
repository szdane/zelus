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

let stability_condition1 = m

let stability_condition2 = (+.) b  kd

let stability_condition3 = (+.) k  kp

let stability_condition4 = ki

let stability_condition5 = (-.) (( *. ) ((+.) b  kd)  ((+.) k  kp)) 
                                (( *. ) m  ki)

type ('c , 'b , 'a) _noise =
  { mutable major_258 : 'c ; mutable v_260 : 'b ; mutable n_259 : 'a }

let noise (cstate_392:Ztypes.cstate) = 
  
  let noise_alloc _ =
    cstate_392.cmax <- (+) cstate_392.cmax  2;
    { major_258 = false ;
      v_260 = { pos = 42.; der = 0. } ; n_259 = { pos = 42.; der = 0. } } in
  let noise_step self ((time_257:float) , ()) =
    ((let (cindex_393:int) = cstate_392.cindex in
      let cpos_395 = ref (cindex_393:int) in
      cstate_392.cindex <- (+) cstate_392.cindex  2 ;
      self.major_258 <- cstate_392.major ;
      (if cstate_392.major then
       for i_1 = cindex_393 to 1 do Zls.set cstate_392.dvec  i_1  0. done
       else ((self.v_260.pos <- Zls.get cstate_392.cvec  !cpos_395 ;
              cpos_395 := (+) !cpos_395  1) ;
             (self.n_259.pos <- Zls.get cstate_392.cvec  !cpos_395 ;
              cpos_395 := (+) !cpos_395  1))) ;
      (let (result_397:float) =
           self.v_260.der <- ( *. ) ((~-.) 25.)  self.n_259.pos ;
           self.n_259.der <- self.v_260.pos ; self.n_259.pos in
       cpos_395 := cindex_393 ;
       (if cstate_392.major then
        (((Zls.set cstate_392.cvec  !cpos_395  self.v_260.pos ;
           cpos_395 := (+) !cpos_395  1) ;
          (Zls.set cstate_392.cvec  !cpos_395  self.n_259.pos ;
           cpos_395 := (+) !cpos_395  1)))
        else (((Zls.set cstate_392.dvec  !cpos_395  self.v_260.der ;
                cpos_395 := (+) !cpos_395  1) ;
               (Zls.set cstate_392.dvec  !cpos_395  self.n_259.der ;
                cpos_395 := (+) !cpos_395  1)))) ; result_397)):float) in 
  let noise_reset self  =
    ((self.n_259.pos <- 0.05 ; self.v_260.pos <- 0.):unit) in
  Node { alloc = noise_alloc; step = noise_step ; reset = noise_reset }
type ('c , 'b , 'a) _sys =
  { mutable major_263 : 'c ; mutable x_265 : 'b ; mutable v_264 : 'a }

let sys (cstate_398:Ztypes.cstate) = 
  
  let sys_alloc _ =
    cstate_398.cmax <- (+) cstate_398.cmax  2;
    { major_263 = false ;
      x_265 = { pos = 42.; der = 0. } ; v_264 = { pos = 42.; der = 0. } } in
  let sys_step self ((time_262:float) , ((u_261:float): float)) =
    ((let (cindex_399:int) = cstate_398.cindex in
      let cpos_401 = ref (cindex_399:int) in
      cstate_398.cindex <- (+) cstate_398.cindex  2 ;
      self.major_263 <- cstate_398.major ;
      (if cstate_398.major then
       for i_1 = cindex_399 to 1 do Zls.set cstate_398.dvec  i_1  0. done
       else ((self.x_265.pos <- Zls.get cstate_398.cvec  !cpos_401 ;
              cpos_401 := (+) !cpos_401  1) ;
             (self.v_264.pos <- Zls.get cstate_398.cvec  !cpos_401 ;
              cpos_401 := (+) !cpos_401  1))) ;
      (let (result_403:(float  * float)) =
           self.v_264.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                      self.x_265.pos) 
                                              (( *. ) b  self.v_264.pos)) 
                                        u_261)  m ;
           self.x_265.der <- self.v_264.pos ;
           (self.x_265.pos , self.v_264.pos) in
       cpos_401 := cindex_399 ;
       (if cstate_398.major then
        (((Zls.set cstate_398.cvec  !cpos_401  self.x_265.pos ;
           cpos_401 := (+) !cpos_401  1) ;
          (Zls.set cstate_398.cvec  !cpos_401  self.v_264.pos ;
           cpos_401 := (+) !cpos_401  1)))
        else (((Zls.set cstate_398.dvec  !cpos_401  self.x_265.der ;
                cpos_401 := (+) !cpos_401  1) ;
               (Zls.set cstate_398.dvec  !cpos_401  self.v_264.der ;
                cpos_401 := (+) !cpos_401  1)))) ; result_403)):float * float) in
  
  let sys_reset self  =
    ((self.v_264.pos <- 0. ; self.x_265.pos <- 0.):unit) in
  Node { alloc = sys_alloc; step = sys_step ; reset = sys_reset }
let pid (((x_268:float): float) ,
         ((v_267:float): float) , ((integral_266:float): float)) =
  let ((error_269:float): float) = (-.) setpoint  x_268 in
  let ((u_270:float): float) =
      (-.) ((+.) (( *. ) kp  error_269)  (( *. ) ki  integral_266)) 
           (( *. ) kd  v_267) in
  (error_269 , u_270)

let pid_esin (((x_274:float): float) ,
              ((v_273:float): float) ,
              ((integral_271:float): float) , ((noise_272:float): float)) =
  let ((error_275:float): float) = (-.) setpoint  ((+.) x_274  noise_272) in
  let ((u_276:float): float) =
      (-.) ((+.) (( *. ) kp  error_275)  (( *. ) ki  integral_271)) 
           (( *. ) kd  ((+.) v_273  0.)) in
  (error_275 , u_276)

let pid_estat (((x_279:float): float) ,
               ((v_278:float): float) , ((integral_277:float): float)) =
  let ((error_280:float): float) = (-.) setpoint  ((-.) x_279  0.5) in
  let ((u_281:float): float) =
      (+.) ((-.) ((+.) (( *. ) kp  error_280)  (( *. ) ki  integral_277)) 
                 (( *. ) kd  ((+.) v_278  0.)))  0. in
  (error_280 , u_281)

let pid_e (((x_285:float): float) ,
           ((v_284:float): float) ,
           ((integral_282:float): float) , ((noise_283:float): float)) =
  let ((error_286:float): float) =
      (-.) setpoint  ((-.) ((+.) x_285  noise_283)  0.5) in
  let ((u_287:float): float) =
      (+.) ((-.) ((+.) (( *. ) kp  error_286)  (( *. ) ki  integral_282)) 
                 (( *. ) kd  ((+.) v_284  0.)))  noise_283 in
  (error_286 , u_287)

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable major_289 : 'e ;
    mutable x_298 : 'd ;
    mutable v_297 : 'c ; mutable t_292 : 'b ; mutable integral_291 : 'a }

let exec (cstate_404:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_404.cmax <- (+) cstate_404.cmax  4;
    { major_289 = false ;
      x_298 = { pos = 42.; der = 0. } ;
      v_297 = { pos = 42.; der = 0. } ;
      t_292 = { pos = 42.; der = 0. } ;
      integral_291 = { pos = 42.; der = 0. } } in
  let exec_step self ((time_288:float) , ()) =
    ((let (cindex_405:int) = cstate_404.cindex in
      let cpos_407 = ref (cindex_405:int) in
      cstate_404.cindex <- (+) cstate_404.cindex  4 ;
      self.major_289 <- cstate_404.major ;
      (if cstate_404.major then
       for i_1 = cindex_405 to 3 do Zls.set cstate_404.dvec  i_1  0. done
       else ((self.x_298.pos <- Zls.get cstate_404.cvec  !cpos_407 ;
              cpos_407 := (+) !cpos_407  1) ;
             (self.v_297.pos <- Zls.get cstate_404.cvec  !cpos_407 ;
              cpos_407 := (+) !cpos_407  1) ;
             (self.t_292.pos <- Zls.get cstate_404.cvec  !cpos_407 ;
              cpos_407 := (+) !cpos_407  1) ;
             (self.integral_291.pos <- Zls.get cstate_404.cvec  !cpos_407 ;
              cpos_407 := (+) !cpos_407  1))) ;
      (let (result_409:(float  * float  * float  * float  * float  * float)) =
           self.t_292.der <- 1. ;
           (let (x_295:float) = self.x_298.pos in
            let (v_294:float) = self.v_297.pos in
            let (((error_290:float): float) , ((u_293:float): float)) =
                pid (x_295 , v_294 , self.integral_291.pos) in
            let ((u_296:float): float) = u_293 in
            self.v_297.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                       self.x_298.pos) 
                                               (( *. ) b  self.v_297.pos)) 
                                         u_296)  m ;
            self.x_298.der <- self.v_297.pos ;
            self.integral_291.der <- error_290 ;
            (x_295 ,
             v_294 ,
             error_290 , self.integral_291.pos , u_293 , self.t_292.pos)) in
       cpos_407 := cindex_405 ;
       (if cstate_404.major then
        (((Zls.set cstate_404.cvec  !cpos_407  self.x_298.pos ;
           cpos_407 := (+) !cpos_407  1) ;
          (Zls.set cstate_404.cvec  !cpos_407  self.v_297.pos ;
           cpos_407 := (+) !cpos_407  1) ;
          (Zls.set cstate_404.cvec  !cpos_407  self.t_292.pos ;
           cpos_407 := (+) !cpos_407  1) ;
          (Zls.set cstate_404.cvec  !cpos_407  self.integral_291.pos ;
           cpos_407 := (+) !cpos_407  1)))
        else (((Zls.set cstate_404.dvec  !cpos_407  self.x_298.der ;
                cpos_407 := (+) !cpos_407  1) ;
               (Zls.set cstate_404.dvec  !cpos_407  self.v_297.der ;
                cpos_407 := (+) !cpos_407  1) ;
               (Zls.set cstate_404.dvec  !cpos_407  self.t_292.der ;
                cpos_407 := (+) !cpos_407  1) ;
               (Zls.set cstate_404.dvec  !cpos_407  self.integral_291.der ;
                cpos_407 := (+) !cpos_407  1)))) ; result_409)):float *
                                                                float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_reset self  =
    ((self.t_292.pos <- 0. ;
      self.x_298.pos <- 0. ;
      self.v_297.pos <- 0. ; self.integral_291.pos <- 0.):unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('f , 'e , 'd , 'c , 'b , 'a) _exec_esin =
  { mutable major_300 : 'f ;
    mutable x_311 : 'e ;
    mutable v_310 : 'd ;
    mutable v_308 : 'c ; mutable n_307 : 'b ; mutable integral_302 : 'a }

let exec_esin (cstate_410:Ztypes.cstate) = 
  
  let exec_esin_alloc _ =
    cstate_410.cmax <- (+) cstate_410.cmax  5;
    { major_300 = false ;
      x_311 = { pos = 42.; der = 0. } ;
      v_310 = { pos = 42.; der = 0. } ;
      v_308 = { pos = 42.; der = 0. } ;
      n_307 = { pos = 42.; der = 0. } ;
      integral_302 = { pos = 42.; der = 0. } } in
  let exec_esin_step self ((time_299:float) , ()) =
    ((let (cindex_411:int) = cstate_410.cindex in
      let cpos_413 = ref (cindex_411:int) in
      cstate_410.cindex <- (+) cstate_410.cindex  5 ;
      self.major_300 <- cstate_410.major ;
      (if cstate_410.major then
       for i_1 = cindex_411 to 4 do Zls.set cstate_410.dvec  i_1  0. done
       else ((self.x_311.pos <- Zls.get cstate_410.cvec  !cpos_413 ;
              cpos_413 := (+) !cpos_413  1) ;
             (self.v_310.pos <- Zls.get cstate_410.cvec  !cpos_413 ;
              cpos_413 := (+) !cpos_413  1) ;
             (self.v_308.pos <- Zls.get cstate_410.cvec  !cpos_413 ;
              cpos_413 := (+) !cpos_413  1) ;
             (self.n_307.pos <- Zls.get cstate_410.cvec  !cpos_413 ;
              cpos_413 := (+) !cpos_413  1) ;
             (self.integral_302.pos <- Zls.get cstate_410.cvec  !cpos_413 ;
              cpos_413 := (+) !cpos_413  1))) ;
      (let (result_415:(float  * float  * float  * float  * float  * float)) =
           let (x_306:float) = self.x_311.pos in
           let (v_305:float) = self.v_310.pos in
           let (n_303:float) = self.n_307.pos in
           let (((error_301:float): float) , ((u_304:float): float)) =
               pid_esin (x_306 , v_305 , self.integral_302.pos , n_303) in
           let ((u_309:float): float) = u_304 in
           self.v_310.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                      self.x_311.pos) 
                                              (( *. ) b  self.v_310.pos)) 
                                        u_309)  m ;
           self.x_311.der <- self.v_310.pos ;
           (let () = () in
            self.v_308.der <- ( *. ) ((~-.) 25.)  self.n_307.pos ;
            self.n_307.der <- self.v_308.pos ;
            self.integral_302.der <- error_301 ;
            (x_306 ,
             v_305 , error_301 , self.integral_302.pos , u_304 , n_303)) in
       cpos_413 := cindex_411 ;
       (if cstate_410.major then
        (((Zls.set cstate_410.cvec  !cpos_413  self.x_311.pos ;
           cpos_413 := (+) !cpos_413  1) ;
          (Zls.set cstate_410.cvec  !cpos_413  self.v_310.pos ;
           cpos_413 := (+) !cpos_413  1) ;
          (Zls.set cstate_410.cvec  !cpos_413  self.v_308.pos ;
           cpos_413 := (+) !cpos_413  1) ;
          (Zls.set cstate_410.cvec  !cpos_413  self.n_307.pos ;
           cpos_413 := (+) !cpos_413  1) ;
          (Zls.set cstate_410.cvec  !cpos_413  self.integral_302.pos ;
           cpos_413 := (+) !cpos_413  1)))
        else (((Zls.set cstate_410.dvec  !cpos_413  self.x_311.der ;
                cpos_413 := (+) !cpos_413  1) ;
               (Zls.set cstate_410.dvec  !cpos_413  self.v_310.der ;
                cpos_413 := (+) !cpos_413  1) ;
               (Zls.set cstate_410.dvec  !cpos_413  self.v_308.der ;
                cpos_413 := (+) !cpos_413  1) ;
               (Zls.set cstate_410.dvec  !cpos_413  self.n_307.der ;
                cpos_413 := (+) !cpos_413  1) ;
               (Zls.set cstate_410.dvec  !cpos_413  self.integral_302.der ;
                cpos_413 := (+) !cpos_413  1)))) ; result_415)):float *
                                                                float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_esin_reset self  =
    ((self.x_311.pos <- 0. ;
      self.v_310.pos <- 0. ;
      self.n_307.pos <- 0.05 ;
      self.integral_302.pos <- 0. ; self.v_308.pos <- 0.):unit) in
  Node { alloc = exec_esin_alloc; step = exec_esin_step ;
                                  reset = exec_esin_reset }
type ('d , 'c , 'b , 'a) _exec_estat =
  { mutable major_313 : 'd ;
    mutable x_321 : 'c ; mutable v_320 : 'b ; mutable integral_315 : 'a }

let exec_estat (cstate_416:Ztypes.cstate) = 
  
  let exec_estat_alloc _ =
    cstate_416.cmax <- (+) cstate_416.cmax  3;
    { major_313 = false ;
      x_321 = { pos = 42.; der = 0. } ;
      v_320 = { pos = 42.; der = 0. } ;
      integral_315 = { pos = 42.; der = 0. } } in
  let exec_estat_step self ((time_312:float) , ()) =
    ((let (cindex_417:int) = cstate_416.cindex in
      let cpos_419 = ref (cindex_417:int) in
      cstate_416.cindex <- (+) cstate_416.cindex  3 ;
      self.major_313 <- cstate_416.major ;
      (if cstate_416.major then
       for i_1 = cindex_417 to 2 do Zls.set cstate_416.dvec  i_1  0. done
       else ((self.x_321.pos <- Zls.get cstate_416.cvec  !cpos_419 ;
              cpos_419 := (+) !cpos_419  1) ;
             (self.v_320.pos <- Zls.get cstate_416.cvec  !cpos_419 ;
              cpos_419 := (+) !cpos_419  1) ;
             (self.integral_315.pos <- Zls.get cstate_416.cvec  !cpos_419 ;
              cpos_419 := (+) !cpos_419  1))) ;
      (let (result_421:(float  * float  * float  * float  * float)) =
           let (x_318:float) = self.x_321.pos in
           let (v_317:float) = self.v_320.pos in
           let (((error_314:float): float) , ((u_316:float): float)) =
               pid_estat (x_318 , v_317 , self.integral_315.pos) in
           let ((u_319:float): float) = u_316 in
           self.v_320.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                      self.x_321.pos) 
                                              (( *. ) b  self.v_320.pos)) 
                                        u_319)  m ;
           self.x_321.der <- self.v_320.pos ;
           self.integral_315.der <- error_314 ;
           (x_318 , v_317 , error_314 , self.integral_315.pos , u_316) in
       cpos_419 := cindex_417 ;
       (if cstate_416.major then
        (((Zls.set cstate_416.cvec  !cpos_419  self.x_321.pos ;
           cpos_419 := (+) !cpos_419  1) ;
          (Zls.set cstate_416.cvec  !cpos_419  self.v_320.pos ;
           cpos_419 := (+) !cpos_419  1) ;
          (Zls.set cstate_416.cvec  !cpos_419  self.integral_315.pos ;
           cpos_419 := (+) !cpos_419  1)))
        else (((Zls.set cstate_416.dvec  !cpos_419  self.x_321.der ;
                cpos_419 := (+) !cpos_419  1) ;
               (Zls.set cstate_416.dvec  !cpos_419  self.v_320.der ;
                cpos_419 := (+) !cpos_419  1) ;
               (Zls.set cstate_416.dvec  !cpos_419  self.integral_315.der ;
                cpos_419 := (+) !cpos_419  1)))) ; result_421)):float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_estat_reset self  =
    ((self.x_321.pos <- 0. ;
      self.v_320.pos <- 0. ; self.integral_315.pos <- 0.):unit) in
  Node { alloc = exec_estat_alloc; step = exec_estat_step ;
                                   reset = exec_estat_reset }
type ('f , 'e , 'd , 'c , 'b , 'a) _exec_e =
  { mutable major_323 : 'f ;
    mutable x_334 : 'e ;
    mutable v_333 : 'd ;
    mutable v_331 : 'c ; mutable n_330 : 'b ; mutable integral_325 : 'a }

let exec_e (cstate_422:Ztypes.cstate) = 
  
  let exec_e_alloc _ =
    cstate_422.cmax <- (+) cstate_422.cmax  5;
    { major_323 = false ;
      x_334 = { pos = 42.; der = 0. } ;
      v_333 = { pos = 42.; der = 0. } ;
      v_331 = { pos = 42.; der = 0. } ;
      n_330 = { pos = 42.; der = 0. } ;
      integral_325 = { pos = 42.; der = 0. } } in
  let exec_e_step self ((time_322:float) , ()) =
    ((let (cindex_423:int) = cstate_422.cindex in
      let cpos_425 = ref (cindex_423:int) in
      cstate_422.cindex <- (+) cstate_422.cindex  5 ;
      self.major_323 <- cstate_422.major ;
      (if cstate_422.major then
       for i_1 = cindex_423 to 4 do Zls.set cstate_422.dvec  i_1  0. done
       else ((self.x_334.pos <- Zls.get cstate_422.cvec  !cpos_425 ;
              cpos_425 := (+) !cpos_425  1) ;
             (self.v_333.pos <- Zls.get cstate_422.cvec  !cpos_425 ;
              cpos_425 := (+) !cpos_425  1) ;
             (self.v_331.pos <- Zls.get cstate_422.cvec  !cpos_425 ;
              cpos_425 := (+) !cpos_425  1) ;
             (self.n_330.pos <- Zls.get cstate_422.cvec  !cpos_425 ;
              cpos_425 := (+) !cpos_425  1) ;
             (self.integral_325.pos <- Zls.get cstate_422.cvec  !cpos_425 ;
              cpos_425 := (+) !cpos_425  1))) ;
      (let (result_427:(float  * float  * float  * float  * float)) =
           let (x_329:float) = self.x_334.pos in
           let (v_328:float) = self.v_333.pos in
           let (n_326:float) = self.n_330.pos in
           let (((error_324:float): float) , ((u_327:float): float)) =
               pid_e (x_329 , v_328 , self.integral_325.pos , n_326) in
           let ((u_332:float): float) = u_327 in
           self.v_333.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                      self.x_334.pos) 
                                              (( *. ) b  self.v_333.pos)) 
                                        u_332)  m ;
           self.x_334.der <- self.v_333.pos ;
           (let () = () in
            self.v_331.der <- ( *. ) ((~-.) 25.)  self.n_330.pos ;
            self.n_330.der <- self.v_331.pos ;
            self.integral_325.der <- error_324 ;
            (x_329 , v_328 , error_324 , self.integral_325.pos , u_327)) in
       cpos_425 := cindex_423 ;
       (if cstate_422.major then
        (((Zls.set cstate_422.cvec  !cpos_425  self.x_334.pos ;
           cpos_425 := (+) !cpos_425  1) ;
          (Zls.set cstate_422.cvec  !cpos_425  self.v_333.pos ;
           cpos_425 := (+) !cpos_425  1) ;
          (Zls.set cstate_422.cvec  !cpos_425  self.v_331.pos ;
           cpos_425 := (+) !cpos_425  1) ;
          (Zls.set cstate_422.cvec  !cpos_425  self.n_330.pos ;
           cpos_425 := (+) !cpos_425  1) ;
          (Zls.set cstate_422.cvec  !cpos_425  self.integral_325.pos ;
           cpos_425 := (+) !cpos_425  1)))
        else (((Zls.set cstate_422.dvec  !cpos_425  self.x_334.der ;
                cpos_425 := (+) !cpos_425  1) ;
               (Zls.set cstate_422.dvec  !cpos_425  self.v_333.der ;
                cpos_425 := (+) !cpos_425  1) ;
               (Zls.set cstate_422.dvec  !cpos_425  self.v_331.der ;
                cpos_425 := (+) !cpos_425  1) ;
               (Zls.set cstate_422.dvec  !cpos_425  self.n_330.der ;
                cpos_425 := (+) !cpos_425  1) ;
               (Zls.set cstate_422.dvec  !cpos_425  self.integral_325.der ;
                cpos_425 := (+) !cpos_425  1)))) ; result_427)):float *
                                                                float *
                                                                float *
                                                                float * float) in
  
  let exec_e_reset self  =
    ((self.x_334.pos <- 0. ;
      self.v_333.pos <- 0. ;
      self.n_330.pos <- 0.05 ;
      self.integral_325.pos <- 0. ; self.v_331.pos <- 0.):unit) in
  Node { alloc = exec_e_alloc; step = exec_e_step ; reset = exec_e_reset }
type ('v ,
      'u ,
      't ,
      's ,
      'r ,
      'q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_336 : 'v ;
    mutable h_390 : 'u ;
    mutable i_388 : 't ;
    mutable h_386 : 's ;
    mutable result_385 : 'r ;
    mutable x_384 : 'q ;
    mutable v_383 : 'p ;
    mutable v_381 : 'o ;
    mutable n_380 : 'n ;
    mutable integral_375 : 'm ;
    mutable x_373 : 'l ;
    mutable v_372 : 'k ;
    mutable integral_367 : 'j ;
    mutable x_365 : 'i ;
    mutable v_364 : 'h ;
    mutable v_362 : 'g ;
    mutable n_361 : 'f ;
    mutable integral_356 : 'e ;
    mutable x_354 : 'd ;
    mutable v_353 : 'c ; mutable t_348 : 'b ; mutable integral_347 : 'a }

let main (cstate_428:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_428.cmax <- (+) cstate_428.cmax  17;
    { major_336 = false ;
      h_390 = 42. ;
      i_388 = (false:bool) ;
      h_386 = (42.:float) ;
      result_385 = (():unit) ;
      x_384 = { pos = 42.; der = 0. } ;
      v_383 = { pos = 42.; der = 0. } ;
      v_381 = { pos = 42.; der = 0. } ;
      n_380 = { pos = 42.; der = 0. } ;
      integral_375 = { pos = 42.; der = 0. } ;
      x_373 = { pos = 42.; der = 0. } ;
      v_372 = { pos = 42.; der = 0. } ;
      integral_367 = { pos = 42.; der = 0. } ;
      x_365 = { pos = 42.; der = 0. } ;
      v_364 = { pos = 42.; der = 0. } ;
      v_362 = { pos = 42.; der = 0. } ;
      n_361 = { pos = 42.; der = 0. } ;
      integral_356 = { pos = 42.; der = 0. } ;
      x_354 = { pos = 42.; der = 0. } ;
      v_353 = { pos = 42.; der = 0. } ;
      t_348 = { pos = 42.; der = 0. } ;
      integral_347 = { pos = 42.; der = 0. } } in
  let main_step self ((time_335:float) , ()) =
    ((let (cindex_429:int) = cstate_428.cindex in
      let cpos_431 = ref (cindex_429:int) in
      cstate_428.cindex <- (+) cstate_428.cindex  17 ;
      self.major_336 <- cstate_428.major ;
      (if cstate_428.major then
       for i_1 = cindex_429 to 16 do Zls.set cstate_428.dvec  i_1  0. done
       else ((self.x_384.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_383.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_381.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.n_380.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.integral_375.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.x_373.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_372.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.integral_367.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.x_365.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_364.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_362.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.n_361.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.integral_356.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.x_354.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.v_353.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.t_348.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1) ;
             (self.integral_347.pos <- Zls.get cstate_428.cvec  !cpos_431 ;
              cpos_431 := (+) !cpos_431  1))) ;
      (let (result_433:unit) =
           let h_389 = ref (infinity:float) in
           (if self.i_388 then self.h_386 <- (+.) time_335  0.) ;
           (let (z_387:bool) =
                (&&) self.major_336  ((>=) time_335  self.h_386) in
            self.h_386 <- (if z_387 then (+.) self.h_386  0.1 else self.h_386)
            ;
            h_389 := min !h_389  self.h_386 ;
            self.h_390 <- !h_389 ;
            self.i_388 <- false ;
            (let () = () in
             let (x_379:float) = self.x_384.pos in
             let (v_378:float) = self.v_383.pos in
             let (n_376:float) = self.n_380.pos in
             let (((error_374:float): float) , ((u_377:float): float)) =
                 pid_e (x_379 , v_378 , self.integral_375.pos , n_376) in
             let ((u_382:float): float) = u_377 in
             self.v_383.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                        self.x_384.pos) 
                                                (( *. ) b  self.v_383.pos)) 
                                          u_382)  m ;
             self.x_384.der <- self.v_383.pos ;
             (let () = () in
              self.v_381.der <- ( *. ) ((~-.) 25.)  self.n_380.pos ;
              self.n_380.der <- self.v_381.pos ;
              self.integral_375.der <- error_374 ;
              (let _ = v_378 in
               let _ = error_374 in
               let _ = self.integral_375.pos in
               let _ = u_377 in
               let () = () in
               let (x_370:float) = self.x_373.pos in
               let (v_369:float) = self.v_372.pos in
               let (((error_366:float): float) , ((u_368:float): float)) =
                   pid_estat (x_370 , v_369 , self.integral_367.pos) in
               let ((u_371:float): float) = u_368 in
               self.v_372.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                          self.x_373.pos) 
                                                  (( *. ) b  self.v_372.pos))
                                             u_371)  m ;
               self.x_373.der <- self.v_372.pos ;
               self.integral_367.der <- error_366 ;
               (let _ = v_369 in
                let _ = error_366 in
                let _ = self.integral_367.pos in
                let _ = u_368 in
                let () = () in
                let (x_360:float) = self.x_365.pos in
                let (v_359:float) = self.v_364.pos in
                let (n_357:float) = self.n_361.pos in
                let (((error_355:float): float) , ((u_358:float): float)) =
                    pid_esin (x_360 , v_359 , self.integral_356.pos , n_357) in
                let ((u_363:float): float) = u_358 in
                self.v_364.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                           self.x_365.pos) 
                                                   (( *. ) b  self.v_364.pos))
                                              u_363)  m ;
                self.x_365.der <- self.v_364.pos ;
                (let () = () in
                 self.v_362.der <- ( *. ) ((~-.) 25.)  self.n_361.pos ;
                 self.n_361.der <- self.v_362.pos ;
                 self.integral_356.der <- error_355 ;
                 (let _ = v_359 in
                  let _ = error_355 in
                  let _ = self.integral_356.pos in
                  let _ = u_358 in
                  let () = () in
                  self.t_348.der <- 1. ;
                  (let (x_351:float) = self.x_354.pos in
                   let (v_350:float) = self.v_353.pos in
                   let (((error_346:float): float) , ((u_349:float): float)) =
                       pid (x_351 , v_350 , self.integral_347.pos) in
                   let ((u_352:float): float) = u_349 in
                   self.v_353.der <- (/.) ((+.) ((-.) (( *. ) ((~-.) k) 
                                                              self.x_354.pos)
                                                      
                                                      (( *. ) b 
                                                              self.v_353.pos))
                                                 u_352)  m ;
                   self.x_354.der <- self.v_353.pos ;
                   self.integral_347.der <- error_346 ;
                   (let _ = error_346 in
                    let _ = self.integral_347.pos in
                    let (x_e_343:float) = x_379 in
                    let (x_estat_345:float) = x_370 in
                    let (x_esin_344:float) = x_360 in
                    let (noise_337:float) = n_357 in
                    let (x_342:float) = x_351 in
                    let (v_341:float) = v_350 in
                    let (u_340:float) = u_349 in
                    let (t_338:float) = self.t_348.pos in
                    let (trigger_339:zero) = z_387 in
                    (begin match trigger_339 with
                           | true ->
                               let _ = print_float x_342 in
                               let _ = print_string "," in
                               let _ = print_float v_341 in
                               let _ = print_string "," in
                               let _ = print_float u_340 in
                               let _ = print_string "," in
                               let _ = print_float x_esin_344 in
                               let _ = print_string "," in
                               let _ = print_float noise_337 in
                               let _ = print_string "," in
                               let _ = print_float x_estat_345 in
                               let _ = print_string "," in
                               let _ = print_float x_e_343 in
                               let (next_391:unit) = print_newline () in
                               self.result_385 <- (if (<) t_338  2.
                                                   then next_391
                                                   else ())
                           | _ -> self.result_385 <- ()  end) ;
                    self.result_385))))))))) in
       cstate_428.horizon <- min cstate_428.horizon  self.h_390 ;
       cpos_431 := cindex_429 ;
       (if cstate_428.major then
        (((Zls.set cstate_428.cvec  !cpos_431  self.x_384.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_383.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_381.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.n_380.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.integral_375.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.x_373.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_372.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.integral_367.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.x_365.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_364.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_362.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.n_361.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.integral_356.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.x_354.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.v_353.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.t_348.pos ;
           cpos_431 := (+) !cpos_431  1) ;
          (Zls.set cstate_428.cvec  !cpos_431  self.integral_347.pos ;
           cpos_431 := (+) !cpos_431  1)))
        else (((Zls.set cstate_428.dvec  !cpos_431  self.x_384.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_383.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_381.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.n_380.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.integral_375.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.x_373.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_372.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.integral_367.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.x_365.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_364.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_362.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.n_361.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.integral_356.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.x_354.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.v_353.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.t_348.der ;
                cpos_431 := (+) !cpos_431  1) ;
               (Zls.set cstate_428.dvec  !cpos_431  self.integral_347.der ;
                cpos_431 := (+) !cpos_431  1)))) ; result_433)):unit) in 
  let main_reset self  =
    ((self.i_388 <- true ;
      self.x_384.pos <- 0. ;
      self.v_383.pos <- 0. ;
      self.n_380.pos <- 0.05 ;
      self.integral_375.pos <- 0. ;
      self.v_381.pos <- 0. ;
      self.x_373.pos <- 0. ;
      self.v_372.pos <- 0. ;
      self.integral_367.pos <- 0. ;
      self.x_365.pos <- 0. ;
      self.v_364.pos <- 0. ;
      self.n_361.pos <- 0.05 ;
      self.integral_356.pos <- 0. ;
      self.v_362.pos <- 0. ;
      self.x_354.pos <- 0. ;
      self.v_353.pos <- 0. ;
      self.integral_347.pos <- 0. ; self.t_348.pos <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
