(* The Zelus compiler, version 2.2-dev
  (2026-02-12-20:23) *)
open Ztypes
let b = true

type ('a) _edge =
  { mutable m_27 : 'a }

let edge  = 
   let edge_alloc _ =
     ();{ m_27 = (false:bool) } in
  let edge_reset self  =
    (self.m_27 <- false:unit) in 
  let edge_step self (b_26:bool) =
    ((let (next_28:bool) = self.m_27 in
      self.m_27 <- b_26 ; next_28):bool) in
  Node { alloc = edge_alloc; reset = edge_reset ; step = edge_step }
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
      h_33 = (42.:float) ; result_32 = (():unit) ; m_40 = (false:bool) } in
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
                        let (b_39:bool) = b in
                        let (next_41:bool) = self.m_40 in
                        self.m_40 <- b_39 ;
                        (let (x_38:bool) = next_41 in
                         let _ = print_string (string_of_bool x_38) in
                         self.result_32 <- print_newline ())
                    | _ -> self.result_32 <- ()  end) ; self.result_32)) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_37 ; result_47)):
    unit) in 
  let main_reset self  =
    ((self.i_35 <- true ; self.m_40 <- false):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
