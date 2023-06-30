(* The Zelus compiler, version 2.2-dev
  (2023-06-20-15:25) *)
open Ztypes
type _main = unit

let main  = 
   let main_alloc _ = () in
  let main_reset self  =
    ((()):unit) in 
  let main_step self () =
    ((let ((y_45:float): float) = 3. in
      let (z_46:float) = (+.) 2.  y_45 in
      let _ = print_float z_46 in
      let ((y_43:float): float) = 3. in
      let (z_44:float) = (-.) 2.  y_43 in
      let _ = print_float z_44 in
      let ((y_41:float): float) = 3. in
      let (z_42:float) = ( *. ) 2.  y_41 in
      let _ = print_float z_42 in
      let ((y_39:float): float) = 3. in
      let (z_40:float) = (/.) 2.  y_39 in
      let _ = print_float z_40 in
      let ((y_37:float): float) = (-3.) in
      let (z_38:float) = (/.) (-2.)  y_37 in
      let _ = print_float z_38 in
      ()):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
