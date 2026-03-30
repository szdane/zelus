(* The Zelus compiler, version 2.2-dev
  (2026-03-30-0:1) *)
open Ztypes
type ('a) _exec1 =
  { mutable m_27 : 'a }

let exec1  = 
   let exec1_alloc _ =
     ();{ m_27 = (42:int) } in
  let exec1_reset self  =
    (self.m_27 <- 1:unit) in 
  let exec1_step self () =
    ((let (next_28:int) = self.m_27 in
      let ((ex_26:int): int) = next_28 in
      self.m_27 <- (+) ex_26  1 ; ex_26):int) in
  Node { alloc = exec1_alloc; reset = exec1_reset ; step = exec1_step }
let dt = 0.1

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
                        let (next_41:int) = self.m_40 in
                        let ((ex_39:int): int) = next_41 in
                        self.m_40 <- (+) ex_39  1 ;
                        (let (x_38:int) = ex_39 in
                         let _ = print_int x_38 in
                         self.result_32 <- print_newline ())
                    | _ -> self.result_32 <- ()  end) ; self.result_32)) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_37 ; result_47)):
    unit) in 
  let main_reset self  =
    ((self.i_35 <- true ; self.m_40 <- 1):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
