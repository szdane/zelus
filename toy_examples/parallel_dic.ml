(* The Zelus compiler, version 2.2-dev
  (2026-09-18-1:27) *)
open Ztypes
type ('a) _simultaneous_reset =
  { mutable x_31 : 'a }

let simultaneous_reset  = 
   let simultaneous_reset_alloc _ =
     ();{ x_31 = (42.:float) } in
  let simultaneous_reset_reset self  =
    (self.x_31 <- 1.:unit) in 
  let simultaneous_reset_step self () =
    ((let (l_33:float) = self.x_31 in
      let (y_32:float) = (+.) l_33  1. in
      self.x_31 <- 1. ; (self.x_31 , y_32)):float * float) in
  Node { alloc = simultaneous_reset_alloc; reset = simultaneous_reset_reset ;
                                           step = simultaneous_reset_step }
let dt = 0.1

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_35 : 'f ;
    mutable h_42 : 'e ;
    mutable i_40 : 'd ;
    mutable h_38 : 'c ; mutable result_37 : 'b ; mutable x_45 : 'a }

let main (cstate_48:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_35 = false ;
      h_42 = 42. ;
      i_40 = (false:bool) ;
      h_38 = (42.:float) ; result_37 = (():unit) ; x_45 = (42.:float) } in
  let main_step self ((time_34:float) , ()) =
    ((self.major_35 <- cstate_48.major ;
      (let (result_53:unit) =
           let h_41 = ref (infinity:float) in
           (if self.i_40 then self.h_38 <- (+.) time_34  0.) ;
           (let (z_39:bool) = (&&) self.major_35  ((>=) time_34  self.h_38) in
            self.h_38 <- (if z_39 then (+.) self.h_38  0.1 else self.h_38) ;
            h_41 := min !h_41  self.h_38 ;
            self.h_42 <- !h_41 ;
            self.i_40 <- false ;
            (let (trigger_36:zero) = z_39 in
             (begin match trigger_36 with
                    | true ->
                        let () = () in
                        let (l_47:float) = self.x_45 in
                        let (y_46:float) = (+.) l_47  1. in
                        let (y_44:float) = y_46 in
                        self.x_45 <- 1. ;
                        (let (x_43:float) = self.x_45 in
                         let _ = print_float x_43 in
                         let _ = print_string " " in
                         let _ = print_float y_44 in
                         self.result_37 <- print_newline ())
                    | _ -> self.result_37 <- ()  end) ; self.result_37)) in
       cstate_48.horizon <- min cstate_48.horizon  self.h_42 ; result_53)):
    unit) in 
  let main_reset self  =
    ((self.i_40 <- true ; self.x_45 <- 1.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
