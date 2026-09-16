(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type ('b , 'a) _main =
  { mutable m_16 : 'b ; mutable m_14 : 'a }

let main  = 
   let main_alloc _ =
     ();{ m_16 = (42:int) ; m_14 = (42:int) } in
  let main_reset self  =
    ((self.m_14 <- (-1) ; self.m_16 <- 0):unit) in 
  let main_step self () =
    ((let (next_15:int) = self.m_14 in
      let ((x_12:int): int) = next_15 in
      self.m_14 <- (~-) x_12 ;
      (let (next_17:int) = self.m_16 in
       let ((y_13:int): int) = next_17 in
       self.m_16 <- (+) y_13  1 ; ())):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
