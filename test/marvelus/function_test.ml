(* The Zelus compiler, version 2.2-dev
  (2023-06-20-15:25) *)
open Ztypes
type _main = unit

let main  = 
   let main_alloc _ = () in
  let main_reset self  =
    ((()):unit) in 
  let main_step self () =
    ((let ((y_79:float): float) = 3. in
      let (z_80:float) = (+.) 2.  y_79 in
      let _ = print_float z_80 in
      let ((y_77:float): float) = 3. in
      let (z_78:float) = (-.) 2.  y_77 in
      let _ = print_float z_78 in
      let ((y_75:float): float) = 3. in
      let (z_76:float) = ( *. ) 2.  y_75 in
      let _ = print_float z_76 in
      let ((y_73:float): float) = 3. in
      let (z_74:float) = (/.) 2.  y_73 in
      let _ = print_float z_74 in
      let ((y_71:float): float) = (-3.) in
      let (z_72:float) = (/.) (-2.)  y_71 in
      let _ = print_float z_72 in
      let ((y_65:float): float) = 3. in
      let (a_66:float) = (+.) 2.  y_65 in
      let (b_67:float) = (+.) a_66  10. in
      let (c_68:float) = ( *. ) b_67  2. in
      let (d_69:float) = (/.) c_68  3. in
      let (z_70:float) = (-.) d_69  2. in
      let _ = print_float z_70 in
      let ((y_63:float): float) = 3. in
      let (z_64:float) =
          (+.) (( *. ) 2.  2.) 
               ((/.) (sqrt ((-.) (( *. ) 2.  2.)  (( *. ) 4.  y_63)))  2.) in
      let _ = print_float z_64 in
      ()):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
