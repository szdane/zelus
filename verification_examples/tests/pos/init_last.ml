(* The Zelus compiler, version 2.2-dev
  (2026-09-16-18:53) *)
open Ztypes
type ('a) _exec =
  { mutable s_28 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ s_28 = (42.:float) } in
  let exec_reset self  =
    (self.s_28 <- 0.:unit) in 
  let exec_step self () =
    ((let (l_30:float) = self.s_28 in
      let ((y_29:float): float) = l_30 in
      let ((copy_44:float): float) = ( *. ) y_29  0.5 in
      self.s_28 <- copy_44 ; y_29):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
let dt = 0.1

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_32 : 'f ;
    mutable h_39 : 'e ;
    mutable i_37 : 'd ;
    mutable h_35 : 'c ; mutable result_34 : 'b ; mutable s_41 : 'a }

let main (cstate_46:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_32 = false ;
      h_39 = 42. ;
      i_37 = (false:bool) ;
      h_35 = (42.:float) ; result_34 = (():unit) ; s_41 = (42.:float) } in
  let main_step self ((time_31:float) , ()) =
    ((self.major_32 <- cstate_46.major ;
      (let (result_51:unit) =
           let h_38 = ref (infinity:float) in
           (if self.i_37 then self.h_35 <- (+.) time_31  0.) ;
           (let (z_36:bool) = (&&) self.major_32  ((>=) time_31  self.h_35) in
            self.h_35 <- (if z_36 then (+.) self.h_35  dt else self.h_35) ;
            h_38 := min !h_38  self.h_35 ;
            self.h_39 <- !h_38 ;
            self.i_37 <- false ;
            (let (trigger_33:zero) = z_36 in
             (begin match trigger_33 with
                    | true ->
                        let () = () in
                        let (l_43:float) = self.s_41 in
                        let ((y_42:float): float) = l_43 in
                        let ((copy_45:float): float) = ( *. ) y_42  0.5 in
                        self.s_41 <- copy_45 ;
                        (let (x_40:float) = y_42 in
                         let _ = print_float x_40 in
                         self.result_34 <- print_newline ())
                    | _ -> self.result_34 <- ()  end) ; self.result_34)) in
       cstate_46.horizon <- min cstate_46.horizon  self.h_39 ; result_51)):
    unit) in 
  let main_reset self  =
    ((self.i_37 <- true ; self.s_41 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
