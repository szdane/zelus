(* The Zelus compiler, version 2.2-dev
  (2026-11-11-20:1) *)
open Ztypes
type ('d , 'c , 'b , 'a) _sawtooth =
  { mutable major_28 : 'd ;
    mutable i_31 : 'c ; mutable next_30 : 'b ; mutable x_29 : 'a }

let sawtooth (cstate_44:Ztypes.cstate) = 
  
  let sawtooth_alloc _ =
    cstate_44.cmax <- (+) cstate_44.cmax  1 ;
    cstate_44.zmax <- (+) cstate_44.zmax  1;
    { major_28 = false ;
      i_31 = (false:bool) ;
      next_30 = { zin = false; zout = 1. } ; x_29 = { pos = 42.; der = 0. } } in
  let sawtooth_step self ((time_27:float) , ()) =
    ((let (cindex_45:int) = cstate_44.cindex in
      let cpos_47 = ref (cindex_45:int) in
      let (zindex_46:int) = cstate_44.zindex in
      let zpos_48 = ref (zindex_46:int) in
      cstate_44.cindex <- (+) cstate_44.cindex  1 ;
      cstate_44.zindex <- (+) cstate_44.zindex  1 ;
      self.major_28 <- cstate_44.major ;
      (if cstate_44.major then
       for i_1 = cindex_45 to 0 do Zls.set cstate_44.dvec  i_1  0. done
       else ((self.x_29.pos <- Zls.get cstate_44.cvec  !cpos_47 ;
              cpos_47 := (+) !cpos_47  1))) ;
      (let (result_49:float) =
           (if self.i_31 then self.x_29.pos <- (0. : float)) ;
           self.i_31 <- false ;
           (begin match self.next_30.zin with
                  | true -> self.x_29.pos <- (0. : float) | _ -> ()  end) ;
           self.next_30.zout <- (-.) self.x_29.pos  1. ;
           self.x_29.der <- 2. ; self.x_29.pos in
       cpos_47 := cindex_45 ;
       (if cstate_44.major then
        (((Zls.set cstate_44.cvec  !cpos_47  self.x_29.pos ;
           cpos_47 := (+) !cpos_47  1)) ; ((self.next_30.zin <- false)))
        else (((self.next_30.zin <- Zls.get_zin cstate_44.zinvec  !zpos_48 ;
                zpos_48 := (+) !zpos_48  1)) ;
              zpos_48 := zindex_46 ;
              ((Zls.set cstate_44.zoutvec  !zpos_48  self.next_30.zout ;
                zpos_48 := (+) !zpos_48  1)) ;
              ((Zls.set cstate_44.dvec  !cpos_47  self.x_29.der ;
                cpos_47 := (+) !cpos_47  1)))) ; result_49)):float) in 
  let sawtooth_reset self  =
    (self.i_31 <- true:unit) in
  Node { alloc = sawtooth_alloc; step = sawtooth_step ;
                                 reset = sawtooth_reset }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable i_43 : 'e ;
    mutable major_33 : 'd ;
    mutable h_42 : 'c ; mutable i_40 : 'b ; mutable h_38 : 'a }

let main (cstate_50:Ztypes.cstate) = 
  let Node { alloc = i_43_alloc; step = i_43_step ; reset = i_43_reset } = sawtooth 
  cstate_50 in
  let main_alloc _ =
    ();
    { major_33 = false ;
      h_42 = 42. ; i_40 = (false:bool) ; h_38 = (42.:float);
      i_43 = i_43_alloc () (* continuous *)  } in
  let main_step self ((time_32:float) , ()) =
    ((self.major_33 <- cstate_50.major ;
      (let (result_55:unit) =
           let h_41 = ref (infinity:float) in
           let resultp_37 = ref (false:bool) in
           let resultv_36 = ref (():unit) in
           (if self.i_40 then self.h_38 <- (+.) time_32  0.) ;
           (let (z_39:bool) = (&&) self.major_33  ((>=) time_32  self.h_38) in
            self.h_38 <- (if z_39 then (+.) self.h_38  0.1 else self.h_38) ;
            h_41 := min !h_41  self.h_38 ;
            self.h_42 <- !h_41 ;
            self.i_40 <- false ;
            (let (trigger_34:zero) = z_39 in
             let (x_35:float) = i_43_step self.i_43 (time_32 , ()) in
             (begin match trigger_34 with
                    | true ->
                        resultp_37 := true ;
                        (let _ = print_float x_35 in
                         resultv_36 := print_newline ()) | _ -> ()  end) ;
             (let _ = (!resultv_36 , !resultp_37) in
              ()))) in
       cstate_50.horizon <- min cstate_50.horizon  self.h_42 ; result_55)):
    unit) in 
  let main_reset self  =
    ((self.i_40 <- true ; i_43_reset self.i_43 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
