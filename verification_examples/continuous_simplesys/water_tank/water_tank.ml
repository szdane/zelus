(* The Zelus compiler, version 2.2-dev
  (2026-11-4-20:25) *)
open Ztypes
type ('c , 'b , 'a) _exec =
  { mutable major_33 : 'c ; mutable s_36 : 'b ; mutable c_34 : 'a }

let exec (cstate_50:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_50.cmax <- (+) cstate_50.cmax  2;
    { major_33 = false ;
      s_36 = { pos = 42.; der = 0. } ; c_34 = { pos = 42.; der = 0. } } in
  let exec_step self ((time_32:float) , ()) =
    ((let (cindex_51:int) = cstate_50.cindex in
      let cpos_53 = ref (cindex_51:int) in
      cstate_50.cindex <- (+) cstate_50.cindex  2 ;
      self.major_33 <- cstate_50.major ;
      (if cstate_50.major then
       for i_1 = cindex_51 to 1 do Zls.set cstate_50.dvec  i_1  0. done
       else ((self.s_36.pos <- Zls.get cstate_50.cvec  !cpos_53 ;
              cpos_53 := (+) !cpos_53  1) ;
             (self.c_34.pos <- Zls.get cstate_50.cvec  !cpos_53 ;
              cpos_53 := (+) !cpos_53  1))) ;
      (let (result_55:float) =
           let (level_35:float) = (+.) 5.  (( *. ) 4.  self.s_36.pos) in
           self.c_34.der <- (/.) ((~-.) self.s_36.pos)  4. ;
           self.s_36.der <- (/.) self.c_34.pos  4. ; level_35 in
       cpos_53 := cindex_51 ;
       (if cstate_50.major then
        (((Zls.set cstate_50.cvec  !cpos_53  self.s_36.pos ;
           cpos_53 := (+) !cpos_53  1) ;
          (Zls.set cstate_50.cvec  !cpos_53  self.c_34.pos ;
           cpos_53 := (+) !cpos_53  1)))
        else (((Zls.set cstate_50.dvec  !cpos_53  self.s_36.der ;
                cpos_53 := (+) !cpos_53  1) ;
               (Zls.set cstate_50.dvec  !cpos_53  self.c_34.der ;
                cpos_53 := (+) !cpos_53  1)))) ; result_55)):float) in 
  let exec_reset self  =
    ((self.s_36.pos <- 0. ; self.c_34.pos <- 1.):unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_38 : 'g ;
    mutable h_49 : 'f ;
    mutable i_47 : 'e ;
    mutable h_45 : 'd ;
    mutable result_44 : 'c ; mutable s_43 : 'b ; mutable c_41 : 'a }

let main (cstate_56:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_56.cmax <- (+) cstate_56.cmax  2;
    { major_38 = false ;
      h_49 = 42. ;
      i_47 = (false:bool) ;
      h_45 = (42.:float) ;
      result_44 = (():unit) ;
      s_43 = { pos = 42.; der = 0. } ; c_41 = { pos = 42.; der = 0. } } in
  let main_step self ((time_37:float) , ()) =
    ((let (cindex_57:int) = cstate_56.cindex in
      let cpos_59 = ref (cindex_57:int) in
      cstate_56.cindex <- (+) cstate_56.cindex  2 ;
      self.major_38 <- cstate_56.major ;
      (if cstate_56.major then
       for i_1 = cindex_57 to 1 do Zls.set cstate_56.dvec  i_1  0. done
       else ((self.s_43.pos <- Zls.get cstate_56.cvec  !cpos_59 ;
              cpos_59 := (+) !cpos_59  1) ;
             (self.c_41.pos <- Zls.get cstate_56.cvec  !cpos_59 ;
              cpos_59 := (+) !cpos_59  1))) ;
      (let (result_61:unit) =
           let h_48 = ref (infinity:float) in
           (if self.i_47 then self.h_45 <- (+.) time_37  0.) ;
           (let (z_46:bool) = (&&) self.major_38  ((>=) time_37  self.h_45) in
            self.h_45 <- (if z_46 then (+.) self.h_45  0.1 else self.h_45) ;
            h_48 := min !h_48  self.h_45 ;
            self.h_49 <- !h_48 ;
            self.i_47 <- false ;
            (let () = () in
             self.c_41.der <- (/.) ((~-.) self.s_43.pos)  4. ;
             self.s_43.der <- (/.) self.c_41.pos  4. ;
             (let (level_42:float) = (+.) 5.  (( *. ) 4.  self.s_43.pos) in
              let (level_39:float) = level_42 in
              let (trigger_40:zero) = z_46 in
              (begin match trigger_40 with
                     | true ->
                         let _ = print_float level_39 in
                         let _ = print_string "," in
                         self.result_44 <- print_newline ()
                     | _ -> self.result_44 <- ()  end) ; self.result_44))) in
       cstate_56.horizon <- min cstate_56.horizon  self.h_49 ;
       cpos_59 := cindex_57 ;
       (if cstate_56.major then
        (((Zls.set cstate_56.cvec  !cpos_59  self.s_43.pos ;
           cpos_59 := (+) !cpos_59  1) ;
          (Zls.set cstate_56.cvec  !cpos_59  self.c_41.pos ;
           cpos_59 := (+) !cpos_59  1)))
        else (((Zls.set cstate_56.dvec  !cpos_59  self.s_43.der ;
                cpos_59 := (+) !cpos_59  1) ;
               (Zls.set cstate_56.dvec  !cpos_59  self.c_41.der ;
                cpos_59 := (+) !cpos_59  1)))) ; result_61)):unit) in 
  let main_reset self  =
    ((self.i_47 <- true ; self.s_43.pos <- 0. ; self.c_41.pos <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
