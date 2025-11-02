(* The Zelus compiler, version 2.2-dev
  (2025-11-2-23:8) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let foo2 = true

let dt = (+.) 0.1  0.3

let ite = if (>) foo  0 then ( * ) (-1)  foo else foo

type ('a) _exec =
  { mutable m_27 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ m_27 = (42:int) } in
  let exec_reset self  =
    (self.m_27 <- 5:unit) in 
  let exec_step self () =
    ((let (x_28:int) = self.m_27 in
      self.m_27 <- 6 ; (let ((e1_26:int): int) = x_28 in
                        7.)):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_30 : 'f ;
    mutable h_37 : 'e ;
    mutable i_35 : 'd ;
    mutable h_33 : 'c ; mutable result_32 : 'b ; mutable m_40 : 'a }

let main (cstate_42:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_30 = false ;
      h_37 = 42. ;
      i_35 = (false:bool) ;
      h_33 = (42.:float) ; result_32 = (():unit) ; m_40 = (42:int) } in
  let main_step self ((time_29:float) , ()) =
    ((self.major_30 <- cstate_42.major ;
      (let (result_47:unit) =
           let h_36 = ref (infinity:float) in
           (if self.i_35 then self.h_33 <- (+.) time_29  0.) ;
           (let (z_34:bool) = (&&) self.major_30  ((>=) time_29  self.h_33) in
            self.h_33 <- (if z_34 then (+.) self.h_33  dt else self.h_33) ;
            h_36 := min !h_36  self.h_33 ;
            self.h_37 <- !h_36 ;
            self.i_35 <- false ;
            (let (trigger_31:zero) = z_34 in
             (begin match trigger_31 with
                    | true ->
                        let () = () in
                        let (x_41:int) = self.m_40 in
                        self.m_40 <- 6 ;
                        (let ((e1_39:int): int) = x_41 in
                         let (x_38:float) = 7. in
                         let _ = print_float x_38 in
                         self.result_32 <- print_newline ())
                    | _ -> self.result_32 <- ()  end) ; self.result_32)) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_37 ; result_47)):
    unit) in 
  let main_reset self  =
    ((self.i_35 <- true ; self.m_40 <- 5):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
