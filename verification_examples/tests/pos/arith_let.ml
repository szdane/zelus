(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type _exec = unit

let exec  = 
   let exec_alloc _ = () in
  let exec_reset self  =
    ((()):unit) in 
  let exec_step self ((x_30:int): int) =
    ((let ((flow_31:int): int) = (+) x_30  6 in
      flow_31):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type _bump = unit

let bump  = 
   let bump_alloc _ = () in
  let bump_reset self  =
    ((()):unit) in 
  let bump_step self ((x_32:int): int) =
    ((let ((y_33:int): int) = (+) x_32  6 in
      y_33):int) in
  Node { alloc = bump_alloc; reset = bump_reset ; step = bump_step }
let dt = 0.1

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_44 : 'f ;
    mutable major_35 : 'e ;
    mutable h_42 : 'd ;
    mutable i_40 : 'c ; mutable h_38 : 'b ; mutable result_37 : 'a }

let main (cstate_45:Ztypes.cstate) = 
  let Node { alloc = i_44_alloc; step = i_44_step ; reset = i_44_reset } = exec 
   in
  let main_alloc _ =
    ();
    { major_35 = false ;
      h_42 = 42. ;
      i_40 = (false:bool) ; h_38 = (42.:float) ; result_37 = (():unit);
      i_44 = i_44_alloc () (* discrete *)  } in
  let main_step self ((time_34:float) , ()) =
    ((self.major_35 <- cstate_45.major ;
      (let (result_50:unit) =
           let h_41 = ref (infinity:float) in
           (if self.i_40 then self.h_38 <- (+.) time_34  0.) ;
           (let (z_39:bool) = (&&) self.major_35  ((>=) time_34  self.h_38) in
            self.h_38 <- (if z_39 then (+.) self.h_38  dt else self.h_38) ;
            h_41 := min !h_41  self.h_38 ;
            self.h_42 <- !h_41 ;
            self.i_40 <- false ;
            (let (trigger_36:zero) = z_39 in
             (begin match trigger_36 with
                    | true ->
                        let (r_43:int) = i_44_step self.i_44 1 in
                        let _ = print_int r_43 in
                        self.result_37 <- print_newline ()
                    | _ -> self.result_37 <- ()  end) ; self.result_37)) in
       cstate_45.horizon <- min cstate_45.horizon  self.h_42 ; result_50)):
    unit) in 
  let main_reset self  =
    ((self.i_40 <- true ; i_44_reset self.i_44 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
