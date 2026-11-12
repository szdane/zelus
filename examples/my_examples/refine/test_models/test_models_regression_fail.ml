(* The Zelus compiler, version 2.2-dev
  (2026-09-18-1:27) *)
open Ztypes
type ('a) _exec =
  { mutable m_24 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ m_24 = (42.:float) } in
  let exec_reset self  =
    (self.m_24 <- 0.:unit) in 
  let exec_step self () =
    ((let (next_25:float) = self.m_24 in
      let ((x_23:float): float) = next_25 in
      self.m_24 <- (-.) x_23  1. ; x_23):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_27 : 'f ;
    mutable h_34 : 'e ;
    mutable i_32 : 'd ;
    mutable h_30 : 'c ; mutable result_29 : 'b ; mutable m_36 : 'a }

let main (cstate_38:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_27 = false ;
      h_34 = 42. ;
      i_32 = (false:bool) ;
      h_30 = (42.:float) ; result_29 = (():unit) ; m_36 = (42.:float) } in
  let main_step self ((time_26:float) , ()) =
    ((self.major_27 <- cstate_38.major ;
      (let (result_43:unit) =
           let h_33 = ref (infinity:float) in
           (if self.i_32 then self.h_30 <- (+.) time_26  0.) ;
           (let (z_31:bool) = (&&) self.major_27  ((>=) time_26  self.h_30) in
            self.h_30 <- (if z_31 then (+.) self.h_30  0.1 else self.h_30) ;
            h_33 := min !h_33  self.h_30 ;
            self.h_34 <- !h_33 ;
            self.i_32 <- false ;
            (let (trigger_28:zero) = z_31 in
             (begin match trigger_28 with
                    | true ->
                        let () = () in
                        let (next_37:float) = self.m_36 in
                        let ((x_35:float): float) = next_37 in
                        self.m_36 <- (-.) x_35  1. ;
                        self.result_29 <- print_float x_35
                    | _ -> self.result_29 <- ()  end) ; self.result_29)) in
       cstate_38.horizon <- min cstate_38.horizon  self.h_34 ; result_43)):
    unit) in 
  let main_reset self  =
    ((self.i_32 <- true ; self.m_36 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
