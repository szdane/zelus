(* The Zelus compiler, version 2.2-dev
  (2026-03-24-4:7) *)
open Ztypes
type ('d , 'c , 'b , 'a) _test_reset =
  { mutable m_40 : 'd ;
    mutable z_38 : 'c ; mutable result_37 : 'b ; mutable x_36 : 'a }

let test_reset  = 
  
  let test_reset_alloc _ =
    ();
    { m_40 = (42:int) ;
      z_38 = (42:int) ; result_37 = (42:int) ; x_36 = (42:int) } in
  let test_reset_reset self  =
    ((self.x_36 <- 0 ; self.m_40 <- 1):unit) in 
  let test_reset_step self () =
    ((let (l_39:int) = self.x_36 in
      (if (>) l_39  5 then self.m_40 <- 1) ;
      (let (next_41:int) = self.m_40 in
       self.z_38 <- next_41 ;
       self.m_40 <- (+) self.z_38  1 ;
       self.result_37 <- self.z_38 ; self.x_36 <- self.result_37 ; self.x_36)):
    int) in
  Node { alloc = test_reset_alloc; reset = test_reset_reset ;
                                   step = test_reset_step }
let dt = 0.1

type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_43 : 'i ;
    mutable h_50 : 'h ;
    mutable i_48 : 'g ;
    mutable h_46 : 'f ;
    mutable result_45 : 'e ;
    mutable m_56 : 'd ;
    mutable z_54 : 'c ; mutable result_53 : 'b ; mutable x_52 : 'a }

let main (cstate_58:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_43 = false ;
      h_50 = 42. ;
      i_48 = (false:bool) ;
      h_46 = (42.:float) ;
      result_45 = (():unit) ;
      m_56 = (42:int) ;
      z_54 = (42:int) ; result_53 = (42:int) ; x_52 = (42:int) } in
  let main_step self ((time_42:float) , ()) =
    ((self.major_43 <- cstate_58.major ;
      (let (result_63:unit) =
           let h_49 = ref (infinity:float) in
           (if self.i_48 then self.h_46 <- (+.) time_42  0.) ;
           (let (z_47:bool) = (&&) self.major_43  ((>=) time_42  self.h_46) in
            self.h_46 <- (if z_47 then (+.) self.h_46  dt else self.h_46) ;
            h_49 := min !h_49  self.h_46 ;
            self.h_50 <- !h_49 ;
            self.i_48 <- false ;
            (let (trigger_44:zero) = z_47 in
             (begin match trigger_44 with
                    | true ->
                        let () = () in
                        let (l_55:int) = self.x_52 in
                        (if (>) l_55  5 then self.m_56 <- 1) ;
                        (let (next_57:int) = self.m_56 in
                         self.z_54 <- next_57 ;
                         self.m_56 <- (+) self.z_54  1 ;
                         self.result_53 <- self.z_54 ;
                         self.x_52 <- self.result_53 ;
                         (let (x_51:int) = self.x_52 in
                          let _ = print_int x_51 in
                          self.result_45 <- print_newline ()))
                    | _ -> self.result_45 <- ()  end) ; self.result_45)) in
       cstate_58.horizon <- min cstate_58.horizon  self.h_50 ; result_63)):
    unit) in 
  let main_reset self  =
    ((self.i_48 <- true ; self.x_52 <- 0 ; self.m_56 <- 1):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
