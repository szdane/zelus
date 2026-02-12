(* The Zelus compiler, version 2.2-dev
  (2026-02-12-20:23) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let ite = if (>=) foo  0 then ( * ) (-1)  foo else foo

type _exec1 = unit

let exec1  = 
   let exec1_alloc _ = () in
  let exec1_reset self  =
    ((()):unit) in 
  let exec1_step self () =
    ((let ((e_22:int): int) = 5 in
      e_22):int) in
  Node { alloc = exec1_alloc; reset = exec1_reset ; step = exec1_step }
let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_24 : 'e ;
    mutable h_31 : 'd ;
    mutable i_29 : 'c ; mutable h_27 : 'b ; mutable result_26 : 'a }

let main (cstate_34:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_24 = false ;
      h_31 = 42. ;
      i_29 = (false:bool) ; h_27 = (42.:float) ; result_26 = (():unit) } in
  let main_step self ((time_23:float) , ()) =
    ((self.major_24 <- cstate_34.major ;
      (let (result_39:unit) =
           let h_30 = ref (infinity:float) in
           (if self.i_29 then self.h_27 <- (+.) time_23  0.) ;
           (let (z_28:bool) = (&&) self.major_24  ((>=) time_23  self.h_27) in
            self.h_27 <- (if z_28 then (+.) self.h_27  dt else self.h_27) ;
            h_30 := min !h_30  self.h_27 ;
            self.h_31 <- !h_30 ;
            self.i_29 <- false ;
            (let (trigger_25:zero) = z_28 in
             (begin match trigger_25 with
                    | true ->
                        let () = () in
                        let ((e_33:int): int) = 5 in
                        let (x_32:int) = e_33 in
                        let _ = print_int x_32 in
                        self.result_26 <- print_newline ()
                    | _ -> self.result_26 <- ()  end) ; self.result_26)) in
       cstate_34.horizon <- min cstate_34.horizon  self.h_31 ; result_39)):
    unit) in  let main_reset self  =
                (self.i_29 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
