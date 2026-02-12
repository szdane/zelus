(* The Zelus compiler, version 2.2-dev
  (2026-02-12-20:23) *)
open Ztypes
type ('a) _hold_first_then =
  { mutable m_41 : 'a }

let hold_first_then  = 
   let hold_first_then_alloc _ =
     ();{ m_41 = (42:int) } in
  let hold_first_then_reset self  =
    (self.m_41 <- 0:unit) in 
  let hold_first_then_step self ((a_40:int): int) =
    ((let (next_42:int) = self.m_41 in
      self.m_41 <- a_40 ; next_42):int) in
  Node { alloc = hold_first_then_alloc; reset = hold_first_then_reset ;
                                        step = hold_first_then_step }
type ('a) _hold_second_then =
  { mutable m_44 : 'a }

let hold_second_then  = 
   let hold_second_then_alloc _ =
     ();{ m_44 = (42:int) } in
  let hold_second_then_reset self  =
    (self.m_44 <- 0:unit) in 
  let hold_second_then_step self ((a_43:int): int) =
    ((let (next_45:int) = self.m_44 in
      self.m_44 <- a_43 ; next_45):int) in
  Node { alloc = hold_second_then_alloc; reset = hold_second_then_reset ;
                                         step = hold_second_then_step }
let dt = 0.1

let b = 5

let c = (-5)

type ('b , 'a) _exec =
  { mutable i_64 : 'b ; mutable m_49 : 'a }

let exec  = 
  let Node { alloc = i_64_alloc; step = i_64_step ; reset = i_64_reset } = hold_first_then 
   in
  let exec_alloc _ =
    ();{ m_49 = (42:int);i_64 = i_64_alloc () (* discrete *)  } in
  let exec_reset self  =
    ((i_64_reset self.i_64  ; self.m_49 <- 0):unit) in 
  let exec_step self () =
    ((let ((y_46:int): int) = i_64_step self.i_64 b in
      let ((a_48:int): int) = c in
      let (next_50:int) = self.m_49 in
      self.m_49 <- a_48 ; (let ((z_47:int): int) = next_50 in
                           z_47)):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_52 : 'f ;
    mutable h_59 : 'e ;
    mutable i_57 : 'd ;
    mutable h_55 : 'c ; mutable result_54 : 'b ; mutable m_62 : 'a }

let main (cstate_65:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_52 = false ;
      h_59 = 42. ;
      i_57 = (false:bool) ;
      h_55 = (42.:float) ; result_54 = (():unit) ; m_62 = (42:int) } in
  let main_step self ((time_51:float) , ()) =
    ((self.major_52 <- cstate_65.major ;
      (let (result_70:unit) =
           let h_58 = ref (infinity:float) in
           (if self.i_57 then self.h_55 <- (+.) time_51  0.) ;
           (let (z_56:bool) = (&&) self.major_52  ((>=) time_51  self.h_55) in
            self.h_55 <- (if z_56 then (+.) self.h_55  dt else self.h_55) ;
            h_58 := min !h_58  self.h_55 ;
            self.h_59 <- !h_58 ;
            self.i_57 <- false ;
            (let (trigger_53:zero) = z_56 in
             (begin match trigger_53 with
                    | true ->
                        let ((a_61:int): int) = b in
                        let (next_63:int) = self.m_62 in
                        self.m_62 <- a_61 ;
                        (let (x_60:int) = next_63 in
                         let _ = print_int x_60 in
                         self.result_54 <- print_newline ())
                    | _ -> self.result_54 <- ()  end) ; self.result_54)) in
       cstate_65.horizon <- min cstate_65.horizon  self.h_59 ; result_70)):
    unit) in 
  let main_reset self  =
    ((self.i_57 <- true ; self.m_62 <- 0):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
