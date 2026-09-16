(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type ('c , 'b , 'a) _model =
  { mutable m_29 : 'c ; mutable m_27 : 'b ; mutable m_25 : 'a }

let model  = 
  
  let model_alloc _ =
    ();{ m_29 = (42:int) ; m_27 = (42:int) ; m_25 = (42:int) } in
  let model_reset self  =
    ((self.m_25 <- 1 ; self.m_29 <- 0 ; self.m_27 <- 0):unit) in 
  let model_step self () =
    ((let (next_26:int) = self.m_25 in
      let (next_30:int) = self.m_29 in
      let (x_24:int) = next_30 in
      self.m_25 <- x_24 ;
      (let (next_28:int) = self.m_27 in
       self.m_27 <- (+) next_26  x_24 ; self.m_29 <- (+) next_28  x_24 ; x_24)):
    int) in
  Node { alloc = model_alloc; reset = model_reset ; step = model_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_40 : 'f ;
    mutable major_32 : 'e ;
    mutable h_39 : 'd ;
    mutable i_37 : 'c ; mutable h_35 : 'b ; mutable result_34 : 'a }

let main (cstate_41:Ztypes.cstate) = 
  let Node { alloc = i_40_alloc; step = i_40_step ; reset = i_40_reset } = model 
   in
  let main_alloc _ =
    ();
    { major_32 = false ;
      h_39 = 42. ;
      i_37 = (false:bool) ; h_35 = (42.:float) ; result_34 = (():unit);
      i_40 = i_40_alloc () (* discrete *)  } in
  let main_step self ((time_31:float) , ()) =
    ((self.major_32 <- cstate_41.major ;
      (let (result_46:unit) =
           let h_38 = ref (infinity:float) in
           (if self.i_37 then self.h_35 <- (+.) time_31  0.) ;
           (let (z_36:bool) = (&&) self.major_32  ((>=) time_31  self.h_35) in
            self.h_35 <- (if z_36 then (+.) self.h_35  0.5 else self.h_35) ;
            h_38 := min !h_38  self.h_35 ;
            self.h_39 <- !h_38 ;
            self.i_37 <- false ;
            (let (trigger_33:zero) = z_36 in
             (begin match trigger_33 with
                    | true ->
                        let _ = print_int (i_40_step self.i_40 ()) in
                        self.result_34 <- print_newline ()
                    | _ -> self.result_34 <- ()  end) ; self.result_34)) in
       cstate_41.horizon <- min cstate_41.horizon  self.h_39 ; result_46)):
    unit) in 
  let main_reset self  =
    ((self.i_37 <- true ; i_40_reset self.i_40 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
