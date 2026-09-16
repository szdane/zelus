(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type ('b , 'a) _integr =
  { mutable i_34 : 'b ; mutable m_31 : 'a }

let integr  = 
   let integr_alloc _ =
     ();{ i_34 = (false:bool) ; m_31 = (42.:float) } in
  let integr_reset self  =
    (self.i_34 <- true:unit) in 
  let integr_step self ((dt_28:float) , (x'_29:float)) =
    ((let (next_32:float) = self.m_31 in
      let (next_33:float) =
          if self.i_34 then 0. else (+.) (( *. ) dt_28  x'_29)  next_32 in
      self.i_34 <- false ;
      (let (x_30:float) = next_33 in
       self.m_31 <- x_30 ; x_30)):float) in
  Node { alloc = integr_alloc; reset = integr_reset ; step = integr_step }
type ('b , 'a) _deriv =
  { mutable i_41 : 'b ; mutable m_38 : 'a }

let deriv  = 
   let deriv_alloc _ =
     ();{ i_41 = (false:bool) ; m_38 = (42.:float) } in
  let deriv_reset self  =
    (self.i_41 <- true:unit) in 
  let deriv_step self ((dt_35:float) , (x_36:float)) =
    ((let (next_39:float) = self.m_38 in
      let (next_40:float) =
          if self.i_41 then 0. else (/.) ((-.) x_36  next_39)  dt_35 in
      self.i_41 <- false ;
      self.m_38 <- x_36 ; (let (x'_37:float) = next_40 in
                           x'_37)):float) in
  Node { alloc = deriv_alloc; reset = deriv_reset ; step = deriv_step }
