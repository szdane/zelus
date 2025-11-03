(* The Zelus compiler, version 2.2-dev
  (2025-11-3-0:6) *)
open Ztypes
let foo = (+) 2  1

let var = foo

let b = true

let foo2 = true

let dt = (+.) 0.1  0.3

let ite = if (>) foo  0 then ( * ) (-1)  foo else foo

type ('b , 'a) _exec =
  { mutable i_36 : 'b ; mutable m_34 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ i_36 = (false:bool) ; m_34 = (42:int) } in
  let exec_reset self  =
    (self.i_36 <- true:unit) in 
  let exec_step self () =
    ((let ((e_32:int): int) = 5 in
      (if self.i_36 then self.m_34 <- e_32) ;
      self.i_36 <- false ;
      (let (x_35:int) = self.m_34 in
       self.m_34 <- 6 ; (let ((e1_33:int): int) = x_35 in
                         7.))):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_38 : 'g ;
    mutable h_45 : 'f ;
    mutable i_43 : 'e ;
    mutable h_41 : 'd ;
    mutable result_40 : 'c ; mutable i_51 : 'b ; mutable m_49 : 'a }

let main (cstate_52:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_38 = false ;
      h_45 = 42. ;
      i_43 = (false:bool) ;
      h_41 = (42.:float) ;
      result_40 = (():unit) ; i_51 = (false:bool) ; m_49 = (42:int) } in
  let main_step self ((time_37:float) , ()) =
    ((self.major_38 <- cstate_52.major ;
      (let (result_57:unit) =
           let h_44 = ref (infinity:float) in
           (if self.i_43 then self.h_41 <- (+.) time_37  0.) ;
           (let (z_42:bool) = (&&) self.major_38  ((>=) time_37  self.h_41) in
            self.h_41 <- (if z_42 then (+.) self.h_41  dt else self.h_41) ;
            h_44 := min !h_44  self.h_41 ;
            self.h_45 <- !h_44 ;
            self.i_43 <- false ;
            (let (trigger_39:zero) = z_42 in
             (begin match trigger_39 with
                    | true ->
                        let ((e_47:int): int) = 5 in
                        (if self.i_51 then self.m_49 <- e_47) ;
                        self.i_51 <- false ;
                        (let () = () in
                         let (x_50:int) = self.m_49 in
                         self.m_49 <- 6 ;
                         (let ((e1_48:int): int) = x_50 in
                          let (x_46:float) = 7. in
                          let _ = print_float x_46 in
                          self.result_40 <- print_newline ()))
                    | _ -> self.result_40 <- ()  end) ; self.result_40)) in
       cstate_52.horizon <- min cstate_52.horizon  self.h_45 ; result_57)):
    unit) in 
  let main_reset self  =
    ((self.i_43 <- true ; self.i_51 <- true):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
