(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let in_rate = 2

type ('a) _exec =
  { mutable m_27 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ m_27 = (42.:float) } in
  let exec_reset self  =
    (self.m_27 <- 0.:unit) in 
  let exec_step self () =
    ((let (next_28:float) = self.m_27 in
      let ((x_26:float): float) = next_28 in
      self.m_27 <- (+.) x_26  (( *. ) (( *. ) 2.  ((-.) 1.  x_26))  0.1) ;
      x_26):float) in
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
      h_33 = (42.:float) ; result_32 = (():unit) ; m_40 = (42.:float) } in
  let main_step self ((time_29:float) , ()) =
    ((self.major_30 <- cstate_42.major ;
      (let (result_47:unit) =
           let h_36 = ref (infinity:float) in
           (if self.i_35 then self.h_33 <- (+.) time_29  0.) ;
           (let (z_34:bool) = (&&) self.major_30  ((>=) time_29  self.h_33) in
            self.h_33 <- (if z_34 then (+.) self.h_33  0.1 else self.h_33) ;
            h_36 := min !h_36  self.h_33 ;
            self.h_37 <- !h_36 ;
            self.i_35 <- false ;
            (let (trigger_31:zero) = z_34 in
             (begin match trigger_31 with
                    | true ->
                        let () = () in
                        let (next_41:float) = self.m_40 in
                        let ((x_39:float): float) = next_41 in
                        self.m_40 <- (+.) x_39 
                                          (( *. ) (( *. ) 2.  ((-.) 1.  x_39))
                                                   0.1) ;
                        (let (x_38:float) = x_39 in
                         let _ = print_float x_38 in
                         self.result_32 <- print_newline ())
                    | _ -> self.result_32 <- ()  end) ; self.result_32)) in
       cstate_42.horizon <- min cstate_42.horizon  self.h_37 ; result_47)):
    unit) in 
  let main_reset self  =
    ((self.i_35 <- true ; self.m_40 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
