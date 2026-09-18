(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
type ('b , 'a) _test =
  { mutable m_32 : 'b ; mutable m_30 : 'a }

let test  = 
   let test_alloc _ =
     ();{ m_32 = (42.:float) ; m_30 = (42.:float) } in
  let test_reset self  =
    ((self.m_32 <- 0. ; self.m_30 <- 0.):unit) in 
  let test_step self () =
    ((let (next_33:float) = self.m_32 in
      let ((zk_29:float): float) = next_33 in
      self.m_32 <- zk_29 ;
      (let (next_31:float) = self.m_30 in
       let ((xk_28:float): float) = next_31 in
       self.m_30 <- xk_28 ; zk_29)):float) in
  Node { alloc = test_alloc; reset = test_reset ; step = test_step }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable major_35 : 'e ;
    mutable h_42 : 'd ;
    mutable i_40 : 'c ; mutable h_38 : 'b ; mutable result_37 : 'a }

let main (cstate_44:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_35 = false ;
      h_42 = 42. ;
      i_40 = (false:bool) ; h_38 = (42.:float) ; result_37 = (():unit) } in
  let main_step self ((time_34:float) , ()) =
    ((self.major_35 <- cstate_44.major ;
      (let (result_49:unit) =
           let h_41 = ref (infinity:float) in
           (if self.i_40 then self.h_38 <- (+.) time_34  0.) ;
           (let (z_39:bool) = (&&) self.major_35  ((>=) time_34  self.h_38) in
            self.h_38 <- (if z_39 then (+.) self.h_38  0.1 else self.h_38) ;
            h_41 := min !h_41  self.h_38 ;
            self.h_42 <- !h_41 ;
            self.i_40 <- false ;
            (let (trigger_36:zero) = z_39 in
             (begin match trigger_36 with
                    | true ->
                        let (x_43:float) = 1. in
                        self.result_37 <- print_newline ()
                    | _ -> self.result_37 <- ()  end) ; self.result_37)) in
       cstate_44.horizon <- min cstate_44.horizon  self.h_42 ; result_49)):
    unit) in  let main_reset self  =
                (self.i_40 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
