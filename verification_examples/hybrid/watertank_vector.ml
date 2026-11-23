(* The Zelus compiler, version 2.2-dev
  (2026-11-23-22:39) *)
open Ztypes
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _tank =
  { mutable major_52 : 'h ;
    mutable h_65 : 'g ;
    mutable h_63 : 'f ;
    mutable i_61 : 'e ;
    mutable next_60 : 'd ;
    mutable next_59 : 'c ;
    mutable derivative_tuple_54 : 'b ; mutable derivative_tuple_53 : 'a }

let tank (cstate_89:Ztypes.cstate) = 
  
  let tank_alloc _ =
    cstate_89.cmax <- (+) cstate_89.cmax  2 ;
    cstate_89.zmax <- (+) cstate_89.zmax  2;
    { major_52 = false ;
      h_65 = 42. ;
      h_63 = (42.:float) ;
      i_61 = (false:bool) ;
      next_60 = { zin = false; zout = 1. } ;
      next_59 = { zin = false; zout = 1. } ;
      derivative_tuple_54 = { pos = 42.; der = 0. } ;
      derivative_tuple_53 = { pos = 42.; der = 0. } } in
  let tank_step self ((time_51:float) , ()) =
    ((let (cindex_90:int) = cstate_89.cindex in
      let cpos_92 = ref (cindex_90:int) in
      let (zindex_91:int) = cstate_89.zindex in
      let zpos_93 = ref (zindex_91:int) in
      cstate_89.cindex <- (+) cstate_89.cindex  2 ;
      cstate_89.zindex <- (+) cstate_89.zindex  2 ;
      self.major_52 <- cstate_89.major ;
      (if cstate_89.major then
       for i_1 = cindex_90 to 1 do Zls.set cstate_89.dvec  i_1  0. done
       else ((self.derivative_tuple_54.pos <- Zls.get cstate_89.cvec 
                                                      !cpos_92 ;
              cpos_92 := (+) !cpos_92  1) ;
             (self.derivative_tuple_53.pos <- Zls.get cstate_89.cvec 
                                                      !cpos_92 ;
              cpos_92 := (+) !cpos_92  1))) ;
      (let (result_94:float) =
           let h_64 = ref (infinity:float) in
           let encore_62 = ref (false:bool) in
           (if self.i_61 then ()) ;
           (let ((derivative_71:float) , (derivative_72:float)) =
                ((5. , 5.) : (float  * float)) in
            self.derivative_tuple_53.pos <- derivative_71 ;
            self.derivative_tuple_54.pos <- derivative_72 ;
            (let (l_57:float) = self.derivative_tuple_53.pos in
             let (l_58:float) = self.derivative_tuple_54.pos in
             (begin match (self.next_59.zin , self.next_60.zin) with
                    | (_ , true) ->
                        let (derivative_tuple_66:float) = l_57 in
                        let ((copy_84:float) , (copy_85:float)) =
                            ((derivative_tuple_66 , (-5.)) : (float  * float)) in
                        self.derivative_tuple_54.pos <- copy_85 ;
                        self.derivative_tuple_53.pos <- copy_84 ;
                        encore_62 := true ;
                        (let (derivative_tuple_67:float) = l_58 in
                         ())
                    | (true , _) ->
                        let (derivative_tuple_68:float) = l_57 in
                        let ((copy_86:float) , (copy_87:float)) =
                            ((derivative_tuple_68 , 5.) : (float  * float)) in
                        self.derivative_tuple_54.pos <- copy_87 ;
                        self.derivative_tuple_53.pos <- copy_86 ;
                        encore_62 := true ;
                        (let (derivative_tuple_69:float) = l_58 in
                         ())
                    | _ -> ()  end) ;
             self.h_63 <- (if !encore_62 then 0. else infinity) ;
             h_64 := min !h_64  self.h_63 ;
             self.h_65 <- !h_64 ;
             self.i_61 <- false ;
             (let (level_55:float) = self.derivative_tuple_53.pos in
              self.next_60.zout <- (-.) level_55  9. ;
              self.next_59.zout <- (-.) 1.  level_55 ;
              (let (rate_56:float) = self.derivative_tuple_54.pos in
               self.derivative_tuple_53.der <- rate_56 ;
               self.derivative_tuple_54.der <- 0. ; level_55)))) in
       cstate_89.horizon <- min cstate_89.horizon  self.h_65 ;
       cpos_92 := cindex_90 ;
       (if cstate_89.major then
        (((Zls.set cstate_89.cvec  !cpos_92  self.derivative_tuple_54.pos ;
           cpos_92 := (+) !cpos_92  1) ;
          (Zls.set cstate_89.cvec  !cpos_92  self.derivative_tuple_53.pos ;
           cpos_92 := (+) !cpos_92  1)) ;
         ((self.next_60.zin <- false) ; (self.next_59.zin <- false)))
        else (((self.next_60.zin <- Zls.get_zin cstate_89.zinvec  !zpos_93 ;
                zpos_93 := (+) !zpos_93  1) ;
               (self.next_59.zin <- Zls.get_zin cstate_89.zinvec  !zpos_93 ;
                zpos_93 := (+) !zpos_93  1)) ;
              zpos_93 := zindex_91 ;
              ((Zls.set cstate_89.zoutvec  !zpos_93  self.next_60.zout ;
                zpos_93 := (+) !zpos_93  1) ;
               (Zls.set cstate_89.zoutvec  !zpos_93  self.next_59.zout ;
                zpos_93 := (+) !zpos_93  1)) ;
              ((Zls.set cstate_89.dvec 
                        !cpos_92  self.derivative_tuple_54.der ;
                cpos_92 := (+) !cpos_92  1) ;
               (Zls.set cstate_89.dvec 
                        !cpos_92  self.derivative_tuple_53.der ;
                cpos_92 := (+) !cpos_92  1)))) ; result_94)):float) in 
  let tank_reset self  =
    (self.i_61 <- true:unit) in
  Node { alloc = tank_alloc; step = tank_step ; reset = tank_reset }
type ('e , 'd , 'c , 'b , 'a) _main =
  { mutable i_88 : 'e ;
    mutable major_74 : 'd ;
    mutable h_83 : 'c ; mutable i_81 : 'b ; mutable h_79 : 'a }

let main (cstate_95:Ztypes.cstate) = 
  let Node { alloc = i_88_alloc; step = i_88_step ; reset = i_88_reset } = tank 
  cstate_95 in
  let main_alloc _ =
    ();
    { major_74 = false ;
      h_83 = 42. ; i_81 = (false:bool) ; h_79 = (42.:float);
      i_88 = i_88_alloc () (* continuous *)  } in
  let main_step self ((time_73:float) , ()) =
    ((self.major_74 <- cstate_95.major ;
      (let (result_100:unit) =
           let h_82 = ref (infinity:float) in
           let resultp_78 = ref (false:bool) in
           let resultv_77 = ref (():unit) in
           (if self.i_81 then self.h_79 <- (+.) time_73  0.) ;
           (let (z_80:bool) = (&&) self.major_74  ((>=) time_73  self.h_79) in
            self.h_79 <- (if z_80 then (+.) self.h_79  0.1 else self.h_79) ;
            h_82 := min !h_82  self.h_79 ;
            self.h_83 <- !h_82 ;
            self.i_81 <- false ;
            (let (trigger_76:zero) = z_80 in
             let (level_75:float) = i_88_step self.i_88 (time_73 , ()) in
             (begin match trigger_76 with
                    | true ->
                        resultp_78 := true ;
                        (let _ = print_float level_75 in
                         resultv_77 := print_newline ()) | _ -> ()  end) ;
             (let _ = (!resultv_77 , !resultp_78) in
              ()))) in
       cstate_95.horizon <- min cstate_95.horizon  self.h_83 ; result_100)):
    unit) in 
  let main_reset self  =
    ((self.i_81 <- true ; i_88_reset self.i_88 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
