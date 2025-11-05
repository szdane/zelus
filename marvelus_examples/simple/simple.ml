(* The Zelus compiler, version 2.2-dev
  (2025-11-5-17:26) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let foo2 = true

let dt = (+.) 0.1  0.3

let ite = if (>) foo  0 then ( * ) (-1)  foo else foo

type ('b , 'a) _exec =
  { mutable i_17 : 'b ; mutable m_15 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_17 = (false:bool) ; m_15 = (42:int) } in
  let exec_reset self  =
    (self.i_17 <- true:unit) in 
  let exec_step self () =
    ((let ((e_13:int): int) = 5 in
      (if self.i_17 then self.m_15 <- e_13) ;
      self.i_17 <- false ;
      (let (x_16:int) = self.m_15 in
       self.m_15 <- 6 ; (let ((e1_14:int): int) = x_16 in
                         e1_14))):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('a) _main =
  { mutable major_19 : 'a }

let main (cstate_20:Ztypes.cstate) = 
   let main_alloc _ =
     ();{ major_19 = false } in
  let main_step self ((time_18:float) , ()) =
    ((self.major_19 <- cstate_20.major):unit) in 
  let main_reset self  =
    ((()):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
