(* The Zelus compiler, version 2.2-dev
  (2026-11-10-17:58) *)
open Ztypes
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _simultaneous_reset =
  { mutable major_40 : 'h ;
    mutable h_50 : 'g ;
    mutable h_48 : 'f ;
    mutable next_46 : 'e ;
    mutable next_45 : 'd ;
    mutable next_44 : 'c ; mutable y_42 : 'b ; mutable x_41 : 'a }

let simultaneous_reset (cstate_64:Ztypes.cstate) = 
  
  let simultaneous_reset_alloc _ =
    cstate_64.cmax <- (+) cstate_64.cmax  2 ;
    cstate_64.zmax <- (+) cstate_64.zmax  3;
    { major_40 = false ;
      h_50 = 42. ;
      h_48 = (42.:float) ;
      next_46 = { zin = false; zout = 1. } ;
      next_45 = { zin = false; zout = 1. } ;
      next_44 = { zin = false; zout = 1. } ;
      y_42 = { pos = 42.; der = 0. } ; x_41 = { pos = 42.; der = 0. } } in
  let simultaneous_reset_step self ((time_39:float) , ()) =
    ((let (cindex_65:int) = cstate_64.cindex in
      let cpos_67 = ref (cindex_65:int) in
      let (zindex_66:int) = cstate_64.zindex in
      let zpos_68 = ref (zindex_66:int) in
      cstate_64.cindex <- (+) cstate_64.cindex  2 ;
      cstate_64.zindex <- (+) cstate_64.zindex  3 ;
      self.major_40 <- cstate_64.major ;
      (if cstate_64.major then
       for i_1 = cindex_65 to 1 do Zls.set cstate_64.dvec  i_1  0. done
       else ((self.y_42.pos <- Zls.get cstate_64.cvec  !cpos_67 ;
              cpos_67 := (+) !cpos_67  1) ;
             (self.x_41.pos <- Zls.get cstate_64.cvec  !cpos_67 ;
              cpos_67 := (+) !cpos_67  1))) ;
      (let (result_69:(float  * float)) =
           let h_49 = ref (infinity:float) in
           let encore_47 = ref (false:bool) in
           let (l_43:float) = self.x_41.pos in
           (begin match (self.next_44.zin , self.next_45.zin) with
                  | (_ , true) -> encore_47 := true ; self.x_41.pos <- 2.
                  | (true , _) -> encore_47 := true ; self.x_41.pos <- 1.5
                  | _ -> ()  end) ;
           self.h_48 <- (if !encore_47 then 0. else infinity) ;
           h_49 := min !h_49  self.h_48 ;
           self.h_50 <- !h_49 ;
           self.next_46.zout <- (-.) l_43  1. ;
           (begin match self.next_46.zin with
                  | true -> self.y_42.pos <- (+.) l_43  1. | _ -> ()  end) ;
           self.y_42.der <- 0. ;
           self.next_45.zout <- (+.) l_43  1. ;
           self.next_44.zout <- (-.) l_43  2. ;
           self.x_41.der <- (-1.) ; (self.x_41.pos , self.y_42.pos) in
       cstate_64.horizon <- min cstate_64.horizon  self.h_50 ;
       cpos_67 := cindex_65 ;
       (if cstate_64.major then
        (((Zls.set cstate_64.cvec  !cpos_67  self.y_42.pos ;
           cpos_67 := (+) !cpos_67  1) ;
          (Zls.set cstate_64.cvec  !cpos_67  self.x_41.pos ;
           cpos_67 := (+) !cpos_67  1)) ;
         ((self.next_46.zin <- false) ;
          (self.next_45.zin <- false) ; (self.next_44.zin <- false)))
        else (((self.next_46.zin <- Zls.get_zin cstate_64.zinvec  !zpos_68 ;
                zpos_68 := (+) !zpos_68  1) ;
               (self.next_45.zin <- Zls.get_zin cstate_64.zinvec  !zpos_68 ;
                zpos_68 := (+) !zpos_68  1) ;
               (self.next_44.zin <- Zls.get_zin cstate_64.zinvec  !zpos_68 ;
                zpos_68 := (+) !zpos_68  1)) ;
              zpos_68 := zindex_66 ;
              ((Zls.set cstate_64.zoutvec  !zpos_68  self.next_46.zout ;
                zpos_68 := (+) !zpos_68  1) ;
               (Zls.set cstate_64.zoutvec  !zpos_68  self.next_45.zout ;
                zpos_68 := (+) !zpos_68  1) ;
               (Zls.set cstate_64.zoutvec  !zpos_68  self.next_44.zout ;
                zpos_68 := (+) !zpos_68  1)) ;
              ((Zls.set cstate_64.dvec  !cpos_67  self.y_42.der ;
                cpos_67 := (+) !cpos_67  1) ;
               (Zls.set cstate_64.dvec  !cpos_67  self.x_41.der ;
                cpos_67 := (+) !cpos_67  1)))) ; result_69)):float * float) in
  
  let simultaneous_reset_reset self  =
    ((self.x_41.pos <- 0. ; self.y_42.pos <- 1.):unit) in
  Node { alloc = simultaneous_reset_alloc; step = simultaneous_reset_step ;
                                           reset = simultaneous_reset_reset }
let dt = 0.1

type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable i_63 : 'e ;
    mutable major_52 : 'd ;
    mutable h_62 : 'c ; mutable i_60 : 'b ; mutable h_58 : 'a }

let main (cstate_70:Ztypes.cstate) = 
  let Node { alloc = i_63_alloc; step = i_63_step ; reset = i_63_reset } = simultaneous_reset 
  cstate_70 in
  let main_alloc _ =
    ();
    { major_52 = false ;
      h_62 = 42. ; i_60 = (false:bool) ; h_58 = (42.:float);
      i_63 = i_63_alloc () (* continuous *)  } in
  let main_step self ((time_51:float) , ()) =
    ((self.major_52 <- cstate_70.major ;
      (let (result_75:unit) =
           let h_61 = ref (infinity:float) in
           let resultp_57 = ref (false:bool) in
           let resultv_56 = ref (():unit) in
           (if self.i_60 then self.h_58 <- (+.) time_51  0.) ;
           (let (z_59:bool) = (&&) self.major_52  ((>=) time_51  self.h_58) in
            self.h_58 <- (if z_59 then (+.) self.h_58  dt else self.h_58) ;
            h_61 := min !h_61  self.h_58 ;
            self.h_62 <- !h_61 ;
            self.i_60 <- false ;
            (let (trigger_53:zero) = z_59 in
             let ((x_54:float) , (y_55:float)) =
                 i_63_step self.i_63 (time_51 , ()) in
             (begin match trigger_53 with
                    | true ->
                        resultp_57 := true ;
                        (let _ = print_float x_54 in
                         let _ = print_string " " in
                         let _ = print_float y_55 in
                         resultv_56 := print_newline ()) | _ -> ()  end) ;
             (let _ = (!resultv_56 , !resultp_57) in
              ()))) in
       cstate_70.horizon <- min cstate_70.horizon  self.h_62 ; result_75)):
    unit) in 
  let main_reset self  =
    ((self.i_60 <- true ; i_63_reset self.i_63 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
