(* The Zelus compiler, version 2.2-dev
  (2026-02-13-23:11) *)
open Ztypes
type state__188 = Unless_A1_18
type state__187 = Unless_A1_13
type ('c , 'b , 'a) _exec =
  { mutable r_35 : 'c ; mutable s_34 : 'b ; mutable x_32 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { r_35 = (false:bool) ;
      s_34 = (Unless_A1_13:state__187) ; x_32 = (42:int) } in
  let exec_reset self  =
    ((self.r_35 <- false ; self.s_34 <- Unless_A1_13 ; self.x_32 <- 0):
    unit) in 
  let exec_step self () =
    ((let (l_33:int) = self.x_32 in
      (begin match self.s_34 with
             | Unless_A1_13 ->
                 (if self.r_35 then ()) ;
                 (begin match (>) l_33  3 with
                        | true ->
                            self.r_35 <- true ; self.s_34 <- Unless_A1_13
                        | _ -> self.r_35 <- false  end) end) ;
      (begin match self.s_34 with
             | Unless_A1_13 ->
                 (if self.r_35 then ()) ; self.x_32 <- (+) l_33  1 end) ;
      self.x_32):int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
let dt = 0.1

type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_37 : 'h ;
    mutable h_44 : 'g ;
    mutable i_42 : 'f ;
    mutable h_40 : 'e ;
    mutable result_39 : 'd ;
    mutable r_49 : 'c ; mutable s_48 : 'b ; mutable x_46 : 'a }

let main (cstate_50:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_37 = false ;
      h_44 = 42. ;
      i_42 = (false:bool) ;
      h_40 = (42.:float) ;
      result_39 = (():unit) ;
      r_49 = (false:bool) ;
      s_48 = (Unless_A1_18:state__188) ; x_46 = (42:int) } in
  let main_step self ((time_36:float) , ()) =
    ((self.major_37 <- cstate_50.major ;
      (let (result_55:unit) =
           let h_43 = ref (infinity:float) in
           (if self.i_42 then self.h_40 <- (+.) time_36  0.) ;
           (let (z_41:bool) = (&&) self.major_37  ((>=) time_36  self.h_40) in
            self.h_40 <- (if z_41 then (+.) self.h_40  dt else self.h_40) ;
            h_43 := min !h_43  self.h_40 ;
            self.h_44 <- !h_43 ;
            self.i_42 <- false ;
            (begin match z_41 with
                   | true ->
                       let (l_47:int) = self.x_46 in
                       (begin match self.s_48 with
                              | Unless_A1_18 ->
                                  (if self.r_49 then ()) ;
                                  (begin match (>) l_47  3 with
                                         | true ->
                                             self.r_49 <- true ;
                                             self.s_48 <- Unless_A1_18
                                         | _ -> self.r_49 <- false  end) end)
                       ;
                       (begin match self.s_48 with
                              | Unless_A1_18 ->
                                  (if self.r_49 then ()) ;
                                  self.x_46 <- (+) l_47  1 end) ;
                       (let _ = print_int self.x_46 in
                        self.result_39 <- print_newline ())
                   | _ -> self.result_39 <- ()  end) ; self.result_39) in
       cstate_50.horizon <- min cstate_50.horizon  self.h_44 ; result_55)):
    unit) in 
  let main_reset self  =
    ((self.i_42 <- true ;
      self.r_49 <- false ; self.s_48 <- Unless_A1_18 ; self.x_46 <- 0):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
