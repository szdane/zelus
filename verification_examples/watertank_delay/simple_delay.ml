(* The Zelus compiler, version 2.2-dev
  (2026-07-7-23:5) *)
open Ztypes
type state__219 = Simple_delay_M2_22 | Simple_delay_M1_21 
type state__218 = Simple_delay_M2_16 | Simple_delay_M1_15 
type ('c , 'b , 'a) _exec =
  { mutable r_39 : 'c ; mutable s_38 : 'b ; mutable delay_36 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { r_39 = (false:bool) ;
      s_38 = (Simple_delay_M2_16:state__218) ; delay_36 = (42.:float) } in
  let exec_reset self  =
    ((self.r_39 <- false ;
      self.s_38 <- Simple_delay_M1_15 ; self.delay_36 <- 0.):unit) in 
  let exec_step self () =
    ((let (l_37:float) = self.delay_36 in
      (begin match self.s_38 with
             | Simple_delay_M1_15 ->
                 (if self.r_39 then ()) ;
                 (begin match (=) l_37  0. with
                        | true ->
                            self.r_39 <- true ;
                            self.s_38 <- Simple_delay_M2_16
                        | _ -> self.r_39 <- false  end)
             | Simple_delay_M2_16 ->
                 (if self.r_39 then ()) ;
                 (begin match (>) l_37  2. with
                        | true ->
                            self.r_39 <- true ;
                            self.s_38 <- Simple_delay_M1_15
                        | _ -> self.r_39 <- false  end)
              end) ;
      (begin match self.s_38 with
             | Simple_delay_M1_15 ->
                 (if self.r_39 then ()) ; self.delay_36 <- 0.
             | Simple_delay_M2_16 ->
                 (if self.r_39 then ()) ; self.delay_36 <- (+.) l_37  1.
              end) ; self.delay_36):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_41 : 'h ;
    mutable h_48 : 'g ;
    mutable i_46 : 'f ;
    mutable h_44 : 'e ;
    mutable result_43 : 'd ;
    mutable r_53 : 'c ; mutable s_52 : 'b ; mutable delay_50 : 'a }

let main (cstate_54:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_41 = false ;
      h_48 = 42. ;
      i_46 = (false:bool) ;
      h_44 = (42.:float) ;
      result_43 = (():unit) ;
      r_53 = (false:bool) ;
      s_52 = (Simple_delay_M2_22:state__219) ; delay_50 = (42.:float) } in
  let main_step self ((time_40:float) , ()) =
    ((self.major_41 <- cstate_54.major ;
      (let (result_59:unit) =
           let h_47 = ref (infinity:float) in
           (if self.i_46 then self.h_44 <- (+.) time_40  0.) ;
           (let (z_45:bool) = (&&) self.major_41  ((>=) time_40  self.h_44) in
            self.h_44 <- (if z_45 then (+.) self.h_44  0.1 else self.h_44) ;
            h_47 := min !h_47  self.h_44 ;
            self.h_48 <- !h_47 ;
            self.i_46 <- false ;
            (let (trigger_42:zero) = z_45 in
             (begin match trigger_42 with
                    | true ->
                        let () = () in
                        let (l_51:float) = self.delay_50 in
                        (begin match self.s_52 with
                               | Simple_delay_M1_21 ->
                                   (if self.r_53 then ()) ;
                                   (begin match (=) l_51  0. with
                                          | true ->
                                              self.r_53 <- true ;
                                              self.s_52 <- Simple_delay_M2_22
                                          | _ -> self.r_53 <- false  end)
                               | Simple_delay_M2_22 ->
                                   (if self.r_53 then ()) ;
                                   (begin match (>) l_51  2. with
                                          | true ->
                                              self.r_53 <- true ;
                                              self.s_52 <- Simple_delay_M1_21
                                          | _ -> self.r_53 <- false  end)
                                end) ;
                        (begin match self.s_52 with
                               | Simple_delay_M1_21 ->
                                   (if self.r_53 then ()) ;
                                   self.delay_50 <- 0.
                               | Simple_delay_M2_22 ->
                                   (if self.r_53 then ()) ;
                                   self.delay_50 <- (+.) l_51  1.
                                end) ;
                        (let (delay_49:float) = self.delay_50 in
                         let _ = print_float delay_49 in
                         self.result_43 <- print_newline ())
                    | _ -> self.result_43 <- ()  end) ; self.result_43)) in
       cstate_54.horizon <- min cstate_54.horizon  self.h_48 ; result_59)):
    unit) in 
  let main_reset self  =
    ((self.i_46 <- true ;
      self.r_53 <- false ;
      self.s_52 <- Simple_delay_M1_21 ; self.delay_50 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
