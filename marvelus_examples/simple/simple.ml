(* The Zelus compiler, version 2.2-dev
  (2025-11-10-6:19) *)
open Ztypes
type ('b , 'a) _exec1 =
  { mutable m_33 : 'b ; mutable m_30 : 'a }

let exec1  = 
  
  let exec1_alloc _ =
    ();
    { m_33 = ((42 , 42 , 42):int * int * int) ; m_30 = ((42 , 42):int * int) } in
  let exec1_reset self  =
    ((self.m_30 <- (3 , 1) ; self.m_33 <- (4 , 5 , 6)):unit) in 
  let exec1_step self () =
    ((let ((e_24:int): int) = 5 in
      let ((x_31:int) , (x_32:int)) = self.m_30 in
      let (((x1_25:int) , (y_26:int)): (int  * int)) = (x_31 , x_32) in
      self.m_30 <- (((+) x1_25  3) , ((+) y_26  1)) ;
      (let ((x_34:int) , (x_35:int) , (x_36:int)) = self.m_33 in
       let (((x1_27:int) , (y_28:int) , (z_29:int)): (int  * int  * int)) =
           (x_34 , x_35 , x_36) in
       self.m_33 <- (x1_27 , y_28 , z_29) ; e_24)):int) in
  Node { alloc = exec1_alloc; reset = exec1_reset ; step = exec1_step }
