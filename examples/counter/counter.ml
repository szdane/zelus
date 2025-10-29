(* The Zelus compiler, version 2.2-dev
  (2025-09-22-16:7) *)
open Ztypes
type ('c , 'b , 'a) _timer =
  { mutable i_38 : 'c ; mutable m_34 : 'b ; mutable i_32 : 'a }

let timer  = 
  
  let timer_alloc _ =
    ();{ i_38 = (false:bool) ; m_34 = (42:int) ; i_32 = (42:int) } in
  let timer_reset self  =
    (self.i_38 <- true:unit) in 
  let timer_step self (x_30:int) =
    ((let (x_36:int) = if self.i_38 then x_30 else self.m_34 in
      let (x_37:int) = if self.i_38 then 0 else (+) 1  self.i_32 in
      self.i_38 <- false ;
      self.m_34 <- max 0  ((-) x_36  1) ;
      self.i_32 <- x_37 ;
      (let _ = print_int x_37 in
       let _ = print_newline () in
       let _ = print_int x_36 in
       let _ = print_newline () in
       (=) x_36  0)):bool) in
  Node { alloc = timer_alloc; reset = timer_reset ; step = timer_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_48 : 'f ;
    mutable major_40 : 'e ;
    mutable h_47 : 'd ;
    mutable i_45 : 'c ; mutable h_43 : 'b ; mutable result_42 : 'a }

let main (cstate_49:Ztypes.cstate) = 
  let Node { alloc = i_48_alloc; step = i_48_step ; reset = i_48_reset } = timer 
   in
  let main_alloc _ =
    ();
    { major_40 = false ;
      h_47 = 42. ;
      i_45 = (false:bool) ; h_43 = (42.:float) ; result_42 = (():unit);
      i_48 = i_48_alloc () (* discrete *)  } in
  let main_step self ((time_39:float) , ()) =
    ((self.major_40 <- cstate_49.major ;
      (let (result_54:unit) =
           let h_46 = ref (infinity:float) in
           (if self.i_45 then self.h_43 <- (+.) time_39  0.) ;
           (let (z_44:bool) = (&&) self.major_40  ((>=) time_39  self.h_43) in
            self.h_43 <- (if z_44 then (+.) self.h_43  0.01 else self.h_43) ;
            h_46 := min !h_46  self.h_43 ;
            self.h_47 <- !h_46 ;
            self.i_45 <- false ;
            (begin match z_44 with
                   | true ->
                       self.result_42 <- print_string (if i_48_step self.i_48
                                                            5
                                                       then "T\n"
                                                       else "F\n")
                   | _ -> self.result_42 <- ()  end) ; self.result_42) in
       cstate_49.horizon <- min cstate_49.horizon  self.h_47 ; result_54)):
    unit) in 
  let main_reset self  =
    ((self.i_45 <- true ; i_48_reset self.i_48 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
