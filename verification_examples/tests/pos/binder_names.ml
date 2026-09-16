(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
let theta = 1.

type _f = unit

let f  = 
   let f_alloc _ = () in
  let f_reset self  =
    ((()):unit) in  let f_step self ((x_27:int): int) =
                      ((+) x_27  6:int) in
  Node { alloc = f_alloc; reset = f_reset ; step = f_step }
type _g = unit

let g  = 
   let g_alloc _ = () in
  let g_reset self  =
    ((()):unit) in  let g_step self ((x_28:int): int) =
                      ((+) x_28  6:int) in
  Node { alloc = g_alloc; reset = g_reset ; step = g_step }
type _noise = unit

let noise  = 
   let noise_alloc _ = () in
  let noise_reset self  =
    ((()):unit) in 
  let noise_step self () =
    ((let ((w_29:float): float) = theta in
      w_29):float) in
  Node { alloc = noise_alloc; reset = noise_reset ; step = noise_step }
let dt = 0.1

type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_40 : 'f ;
    mutable major_31 : 'e ;
    mutable h_38 : 'd ;
    mutable i_36 : 'c ; mutable h_34 : 'b ; mutable result_33 : 'a }

let main (cstate_41:Ztypes.cstate) = 
  let Node { alloc = i_40_alloc; step = i_40_step ; reset = i_40_reset } = f 
   in
  let main_alloc _ =
    ();
    { major_31 = false ;
      h_38 = 42. ;
      i_36 = (false:bool) ; h_34 = (42.:float) ; result_33 = (():unit);
      i_40 = i_40_alloc () (* discrete *)  } in
  let main_step self ((time_30:float) , ()) =
    ((self.major_31 <- cstate_41.major ;
      (let (result_46:unit) =
           let h_37 = ref (infinity:float) in
           (if self.i_36 then self.h_34 <- (+.) time_30  0.) ;
           (let (z_35:bool) = (&&) self.major_31  ((>=) time_30  self.h_34) in
            self.h_34 <- (if z_35 then (+.) self.h_34  dt else self.h_34) ;
            h_37 := min !h_37  self.h_34 ;
            self.h_38 <- !h_37 ;
            self.i_36 <- false ;
            (let (trigger_32:zero) = z_35 in
             (begin match trigger_32 with
                    | true ->
                        let (r_39:int) = i_40_step self.i_40 1 in
                        let _ = print_int r_39 in
                        self.result_33 <- print_newline ()
                    | _ -> self.result_33 <- ()  end) ; self.result_33)) in
       cstate_41.horizon <- min cstate_41.horizon  self.h_38 ; result_46)):
    unit) in 
  let main_reset self  =
    ((self.i_36 <- true ; i_40_reset self.i_40 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
