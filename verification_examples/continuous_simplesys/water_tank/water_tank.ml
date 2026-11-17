(* The Zelus compiler, version 2.2-dev
  (2026-11-16-20:34) *)
open Ztypes
type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable major_34 : 'e ;
    mutable i_39 : 'd ;
    mutable next_38 : 'c ; mutable next_37 : 'b ; mutable x_36 : 'a }

let exec (cstate_54:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_54.cmax <- (+) cstate_54.cmax  1 ;
    cstate_54.zmax <- (+) cstate_54.zmax  2;
    { major_34 = false ;
      i_39 = (false:bool) ;
      next_38 = { zin = false; zout = 1. } ;
      next_37 = { zin = false; zout = 1. } ; x_36 = { pos = 42.; der = 0. } } in
  let exec_step self ((time_33:float) , ()) =
    ((let (cindex_55:int) = cstate_54.cindex in
      let cpos_57 = ref (cindex_55:int) in
      let (zindex_56:int) = cstate_54.zindex in
      let zpos_58 = ref (zindex_56:int) in
      cstate_54.cindex <- (+) cstate_54.cindex  1 ;
      cstate_54.zindex <- (+) cstate_54.zindex  2 ;
      self.major_34 <- cstate_54.major ;
      (if cstate_54.major then
       for i_1 = cindex_55 to 0 do Zls.set cstate_54.dvec  i_1  0. done
       else ((self.x_36.pos <- Zls.get cstate_54.cvec  !cpos_57 ;
              cpos_57 := (+) !cpos_57  1))) ;
      (let (result_59:float) =
           (if self.i_39 then self.x_36.pos <- (1. : float)) ;
           self.i_39 <- false ;
           (begin match (self.next_37.zin , self.next_38.zin) with
                  | (_ , true) -> self.x_36.pos <- ((-3.) : float)
                  | (true , _) -> self.x_36.pos <- (1. : float) | _ -> ()  end)
           ;
           (let ((level_35:float): float) =
                ( *. ) self.x_36.pos  self.x_36.pos in
            self.next_38.zout <- (-.) self.x_36.pos  3. ;
            self.next_37.zout <- (+.) self.x_36.pos  1. ;
            self.x_36.der <- 2. ; level_35) in
       cpos_57 := cindex_55 ;
       (if cstate_54.major then
        (((Zls.set cstate_54.cvec  !cpos_57  self.x_36.pos ;
           cpos_57 := (+) !cpos_57  1)) ;
         ((self.next_38.zin <- false) ; (self.next_37.zin <- false)))
        else (((self.next_38.zin <- Zls.get_zin cstate_54.zinvec  !zpos_58 ;
                zpos_58 := (+) !zpos_58  1) ;
               (self.next_37.zin <- Zls.get_zin cstate_54.zinvec  !zpos_58 ;
                zpos_58 := (+) !zpos_58  1)) ;
              zpos_58 := zindex_56 ;
              ((Zls.set cstate_54.zoutvec  !zpos_58  self.next_38.zout ;
                zpos_58 := (+) !zpos_58  1) ;
               (Zls.set cstate_54.zoutvec  !zpos_58  self.next_37.zout ;
                zpos_58 := (+) !zpos_58  1)) ;
              ((Zls.set cstate_54.dvec  !cpos_57  self.x_36.der ;
                cpos_57 := (+) !cpos_57  1)))) ; result_59)):float) in 
  let exec_reset self  =
    (self.i_39 <- true:unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_41 : 'h ;
    mutable h_53 : 'g ;
    mutable i_51 : 'f ;
    mutable next_50 : 'e ;
    mutable next_49 : 'd ;
    mutable h_47 : 'c ; mutable result_46 : 'b ; mutable x_45 : 'a }

let main (cstate_60:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_60.cmax <- (+) cstate_60.cmax  1 ;
    cstate_60.zmax <- (+) cstate_60.zmax  2;
    { major_41 = false ;
      h_53 = 42. ;
      i_51 = (false:bool) ;
      next_50 = { zin = false; zout = 1. } ;
      next_49 = { zin = false; zout = 1. } ;
      h_47 = (42.:float) ;
      result_46 = (():unit) ; x_45 = { pos = 42.; der = 0. } } in
  let main_step self ((time_40:float) , ()) =
    ((let (cindex_61:int) = cstate_60.cindex in
      let cpos_63 = ref (cindex_61:int) in
      let (zindex_62:int) = cstate_60.zindex in
      let zpos_64 = ref (zindex_62:int) in
      cstate_60.cindex <- (+) cstate_60.cindex  1 ;
      cstate_60.zindex <- (+) cstate_60.zindex  2 ;
      self.major_41 <- cstate_60.major ;
      (if cstate_60.major then
       for i_1 = cindex_61 to 0 do Zls.set cstate_60.dvec  i_1  0. done
       else ((self.x_45.pos <- Zls.get cstate_60.cvec  !cpos_63 ;
              cpos_63 := (+) !cpos_63  1))) ;
      (let (result_65:unit) =
           let h_52 = ref (infinity:float) in
           (if self.i_51 then self.h_47 <- (+.) time_40  0.) ;
           (let (z_48:bool) = (&&) self.major_41  ((>=) time_40  self.h_47) in
            self.h_47 <- (if z_48 then (+.) self.h_47  0.1 else self.h_47) ;
            h_52 := min !h_52  self.h_47 ;
            self.h_53 <- !h_52 ;
            (if self.i_51 then self.x_45.pos <- (1. : float)) ;
            self.i_51 <- false ;
            (let () = () in
             (begin match (self.next_49.zin , self.next_50.zin) with
                    | (_ , true) -> self.x_45.pos <- ((-3.) : float)
                    | (true , _) -> self.x_45.pos <- (1. : float) | _ -> ()  end)
             ;
             self.next_50.zout <- (-.) self.x_45.pos  3. ;
             self.next_49.zout <- (+.) self.x_45.pos  1. ;
             self.x_45.der <- 2. ;
             (let ((level_44:float): float) =
                  ( *. ) self.x_45.pos  self.x_45.pos in
              let (level_42:float) = level_44 in
              let (trigger_43:zero) = z_48 in
              (begin match trigger_43 with
                     | true ->
                         let _ = print_float level_42 in
                         self.result_46 <- print_newline ()
                     | _ -> self.result_46 <- ()  end) ; self.result_46))) in
       cstate_60.horizon <- min cstate_60.horizon  self.h_53 ;
       cpos_63 := cindex_61 ;
       (if cstate_60.major then
        (((Zls.set cstate_60.cvec  !cpos_63  self.x_45.pos ;
           cpos_63 := (+) !cpos_63  1)) ;
         ((self.next_50.zin <- false) ; (self.next_49.zin <- false)))
        else (((self.next_50.zin <- Zls.get_zin cstate_60.zinvec  !zpos_64 ;
                zpos_64 := (+) !zpos_64  1) ;
               (self.next_49.zin <- Zls.get_zin cstate_60.zinvec  !zpos_64 ;
                zpos_64 := (+) !zpos_64  1)) ;
              zpos_64 := zindex_62 ;
              ((Zls.set cstate_60.zoutvec  !zpos_64  self.next_50.zout ;
                zpos_64 := (+) !zpos_64  1) ;
               (Zls.set cstate_60.zoutvec  !zpos_64  self.next_49.zout ;
                zpos_64 := (+) !zpos_64  1)) ;
              ((Zls.set cstate_60.dvec  !cpos_63  self.x_45.der ;
                cpos_63 := (+) !cpos_63  1)))) ; result_65)):unit) in 
  let main_reset self  =
    (self.i_51 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
