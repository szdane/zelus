(* The Zelus compiler, version 2.2-dev
  (2023-10-14-18:6) *)
open Ztypes
let add (((x_11:float) , (y_12:float)): (float  * float)) =
  (+.) x_11  y_12

type _main = unit

let main  = 
   let main_alloc _ = () in
  let main_reset self  =
    ((()):unit) in  let main_step self () =
                      (():unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
