(* The Zelus compiler, version 2.2-dev
  (2025-11-14-1:57) *)
open Ztypes
type _ite_let_ok = unit

let ite_let_ok  = 
   let ite_let_ok_alloc _ = () in
  let ite_let_ok_reset self  =
    ((()):unit) in 
  let ite_let_ok_step self () =
    ((let ((foo_26:int): int) = 2 in
      let ((z_27:int): int) =
          if (>=) foo_26  0 then ( * ) (-1)  foo_26 else foo_26 in
      z_27):int) in
  Node { alloc = ite_let_ok_alloc; reset = ite_let_ok_reset ;
                                   step = ite_let_ok_step }
let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_29 : 'e ;
    mutable h_36 : 'd ;
    mutable i_34 : 'c ; mutable h_32 : 'b ; mutable result_31 : 'a }

let main (cstate_40:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_29 = false ;
      h_36 = 42. ;
      i_34 = (false:bool) ; h_32 = (42.:float) ; result_31 = (():unit) } in
  let main_step self ((time_28:float) , ()) =
    ((self.major_29 <- cstate_40.major ;
      (let (result_45:unit) =
           let h_35 = ref (infinity:float) in
           (if self.i_34 then self.h_32 <- (+.) time_28  0.) ;
           (let (z_33:bool) = (&&) self.major_29  ((>=) time_28  self.h_32) in
            self.h_32 <- (if z_33 then (+.) self.h_32  dt else self.h_32) ;
            h_35 := min !h_35  self.h_32 ;
            self.h_36 <- !h_35 ;
            self.i_34 <- false ;
            (let (trigger_30:zero) = z_33 in
             (begin match trigger_30 with
                    | true ->
                        let () = () in
                        let ((foo_38:int): int) = 2 in
                        let ((z_39:int): int) =
                            if (>=) foo_38  0
                            then ( * ) (-1)  foo_38
                            else foo_38 in
                        let (x_37:int) = z_39 in
                        let _ = print_int x_37 in
                        self.result_31 <- print_newline ()
                    | _ -> self.result_31 <- ()  end) ; self.result_31)) in
       cstate_40.horizon <- min cstate_40.horizon  self.h_36 ; result_45)):
    unit) in  let main_reset self  =
                (self.i_34 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
