(* The Zelus compiler, version 2.2-dev
  (2025-11-7-20:46) *)
open Ztypes
let five = (-) ((+) 2  3)  0

let five' = 5

let foo = 3

let ite_ok = if (>=) foo  0 then ( * ) (-1)  foo else foo

type _ite_let_ok = unit

let ite_let_ok  = 
   let ite_let_ok_alloc _ = () in
  let ite_let_ok_reset self  =
    ((()):unit) in 
  let ite_let_ok_step self () =
    ((let ((foo_34:int): int) = 2 in
      let ((z_35:int): int) =
          if (>=) foo_34  0 then ( * ) (-1)  foo_34 else foo_34 in
      z_35):int) in
  Node { alloc = ite_let_ok_alloc; reset = ite_let_ok_reset ;
                                   step = ite_let_ok_step }
type ('a) _hold_first_then =
  { mutable m_37 : 'a }

let hold_first_then  = 
   let hold_first_then_alloc _ =
     ();{ m_37 = (42:int) } in
  let hold_first_then_reset self  =
    (self.m_37 <- 0:unit) in 
  let hold_first_then_step self ((a_36:int): int) =
    ((let (x_38:int) = self.m_37 in
      self.m_37 <- a_36 ; x_38):int) in
  Node { alloc = hold_first_then_alloc; reset = hold_first_then_reset ;
                                        step = hold_first_then_step }
let b = true

type ('a) _edge =
  { mutable m_40 : 'a }

let edge  = 
   let edge_alloc _ =
     ();{ m_40 = (false:bool) } in
  let edge_reset self  =
    (self.m_40 <- false:unit) in 
  let edge_step self (b_39:bool) =
    ((let (x_41:bool) = self.m_40 in
      self.m_40 <- b_39 ; x_41):bool) in
  Node { alloc = edge_alloc; reset = edge_reset ; step = edge_step }
let ok_tmp = 7

let pin = ok_tmp

let dt = 0.1

let a = 5

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_43 : 'e ;
    mutable h_50 : 'd ;
    mutable i_48 : 'c ; mutable h_46 : 'b ; mutable result_45 : 'a }

let main (cstate_52:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_43 = false ;
      h_50 = 42. ;
      i_48 = (false:bool) ; h_46 = (42.:float) ; result_45 = (():unit) } in
  let main_step self ((time_42:float) , ()) =
    ((self.major_43 <- cstate_52.major ;
      (let (result_57:unit) =
           let h_49 = ref (infinity:float) in
           (if self.i_48 then self.h_46 <- (+.) time_42  0.) ;
           (let (z_47:bool) = (&&) self.major_43  ((>=) time_42  self.h_46) in
            self.h_46 <- (if z_47 then (+.) self.h_46  dt else self.h_46) ;
            h_49 := min !h_49  self.h_46 ;
            self.h_50 <- !h_49 ;
            self.i_48 <- false ;
            (let (trigger_44:zero) = z_47 in
             (begin match trigger_44 with
                    | true ->
                        let (x_51:int) = pin in
                        let _ = print_int x_51 in
                        self.result_45 <- print_newline ()
                    | _ -> self.result_45 <- ()  end) ; self.result_45)) in
       cstate_52.horizon <- min cstate_52.horizon  self.h_50 ; result_57)):
    unit) in  let main_reset self  =
                (self.i_48 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
