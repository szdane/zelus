(* The Zelus compiler, version 2.2-dev
  (2025-11-7-20:23) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let dt = (+.) 0.1  0.3

let ite = if (>=) foo  0 then ( * ) (-1)  foo else foo

type _exec1 = unit

let exec1  = 
   let exec1_alloc _ = () in
  let exec1_reset self  =
    ((()):unit) in 
  let exec1_step self () =
    ((let ((n_34:int): int) = 5 in
      let ((e_33:int): int) = 5 in
      let (((x1_35:int) , (y_36:int) , (z_37:int)): (int  * int  * int)) =
          (4 , 5 , 6) in
      e_33):int) in
  Node { alloc = exec1_alloc; reset = exec1_reset ; step = exec1_step }
type ('b , 'a) _exec =
  { mutable i_42 : 'b ; mutable m_40 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_42 = (false:bool) ; m_40 = (42:int) } in
  let exec_reset self  =
    (self.i_42 <- true:unit) in 
  let exec_step self () =
    ((let ((e_38:int): int) = if (>) foo  0 then foo else ( * ) (-1)  foo in
      (if self.i_42 then self.m_40 <- e_38) ;
      self.i_42 <- false ;
      (let (x_41:int) = self.m_40 in
       self.m_40 <- 6 ; (let ((e1_39:int): int) = x_41 in
                         e1_39))):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('a) _edge =
  { mutable m_44 : 'a }

let edge  = 
   let edge_alloc _ =
     ();{ m_44 = (false:bool) } in
  let edge_reset self  =
    (self.m_44 <- false:unit) in 
  let edge_step self (b_43:bool) =
    ((let (x_45:bool) = self.m_44 in
      self.m_44 <- b_43 ; x_45):bool) in
  Node { alloc = edge_alloc; reset = edge_reset ; step = edge_step }
type ('a) _main =
  { mutable major_47 : 'a }

let main (cstate_48:Ztypes.cstate) = 
   let main_alloc _ =
     ();{ major_47 = false } in
  let main_step self ((time_46:float) , ()) =
    ((self.major_47 <- cstate_48.major):unit) in 
  let main_reset self  =
    ((()):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
