(* The Zelus compiler, version 2.2-dev
  (2025-08-5-17:44) *)
open Ztypes
let dt = 0.1

type ('a) _main =
  { mutable major_5 : 'a }

let main (cstate_6:Ztypes.cstate) = 
   let main_alloc _ =
     ();{ major_5 = false } in
  let main_step self ((time_4:float) , ()) =
    ((self.major_5 <- cstate_6.major):unit) in 
  let main_reset self  =
    ((()):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
