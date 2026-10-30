(* The Zelus compiler, version 2.2-dev
  (2026-09-18-1:27) *)
open Ztypes
let a = 1.

type ('b , 'a) _test =
  { mutable i_31 : 'b ; mutable m_29 : 'a }

let test  = 
   let test_alloc _ =
     ();{ i_31 = (false:bool) ; m_29 = (42.:float) } in
  let test_reset self  =
    (self.i_31 <- true:unit) in 
  let test_step self () =
    (((if self.i_31 then self.m_29 <- a) ;
      self.i_31 <- false ;
      (let (next_30:float) = self.m_29 in
       let ((t_28:float): float) = next_30 in
       self.m_29 <- t_28 ; t_28)):float) in
  Node { alloc = test_alloc; reset = test_reset ; step = test_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_33 : 'g ;
    mutable h_40 : 'f ;
    mutable i_38 : 'e ;
    mutable h_36 : 'd ;
    mutable result_35 : 'c ; mutable i_45 : 'b ; mutable m_43 : 'a }

let main (cstate_46:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_33 = false ;
      h_40 = 42. ;
      i_38 = (false:bool) ;
      h_36 = (42.:float) ;
      result_35 = (():unit) ; i_45 = (false:bool) ; m_43 = (42.:float) } in
  let main_step self ((time_32:float) , ()) =
    ((self.major_33 <- cstate_46.major ;
      (let (result_51:unit) =
           let h_39 = ref (infinity:float) in
           (if self.i_38 then self.h_36 <- (+.) time_32  0.) ;
           (let (z_37:bool) = (&&) self.major_33  ((>=) time_32  self.h_36) in
            self.h_36 <- (if z_37 then (+.) self.h_36  0.1 else self.h_36) ;
            h_39 := min !h_39  self.h_36 ;
            self.h_40 <- !h_39 ;
            self.i_38 <- false ;
            (let (trigger_34:zero) = z_37 in
             (begin match trigger_34 with
                    | true ->
                        (if self.i_45 then self.m_43 <- a) ;
                        self.i_45 <- false ;
                        (let () = () in
                         let (next_44:float) = self.m_43 in
                         let ((t_42:float): float) = next_44 in
                         self.m_43 <- t_42 ;
                         (let (x_41:float) = t_42 in
                          let _ = print_float x_41 in
                          self.result_35 <- print_newline ()))
                    | _ -> self.result_35 <- ()  end) ; self.result_35)) in
       cstate_46.horizon <- min cstate_46.horizon  self.h_40 ; result_51)):
    unit) in 
  let main_reset self  =
    ((self.i_38 <- true ; self.i_45 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
