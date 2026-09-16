(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type ('a) _main =
  { mutable m_8 : 'a }

let main  = 
   let main_alloc _ =
     ();{ m_8 = (42:int) } in
  let main_reset self  =
    (self.m_8 <- 5:unit) in 
  let main_step self () =
    ((let (next_9:int) = self.m_8 in
      let ((xf_7:int): int) = next_9 in
      self.m_8 <- (if (<) xf_7  1 then (+) xf_7  1 else (-) xf_7  1) ; xf_7):
    int) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
