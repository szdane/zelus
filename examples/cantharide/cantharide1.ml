(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type state__945 = Cantharide1_Finished_60 | Cantharide1_Running_59 
type state__944 =
Cantharide1_TowardBarcelona_56 | Cantharide1_TowardGirona_55 
let barcelona = 0.

let girona = 100.

let fly_velocity = 80.

let car_velocity = 50.

type _print_status = unit

let print_status  = 
   let print_status_alloc _ = () in
  let print_status_reset self  =
    ((()):unit) in 
  let print_status_step self ((eventname_95:string) ,
                              (car1_93:float) ,
                              (car2_94:float) ,
                              (fly_96:float) , (zigzags_97:int)) =
    ((let _ = flush stdout in
      print_endline ((^) eventname_95 
                         ((^) ": car1=" 
                              ((^) (string_of_float car1_93) 
                                   ((^) "; car2=" 
                                        ((^) (string_of_float car2_94) 
                                             ((^) "; fly=" 
                                                  ((^) (string_of_float 
                                                          fly_96) 
                                                       ((^) "; zigzags=" 
                                                            (string_of_float 
                                                               ((/.) 
                                                                  (float 
                                                                    zigzags_97)
                                                                   2.))))))))))):
    unit) in
  Node { alloc = print_status_alloc; reset = print_status_reset ;
                                     step = print_status_step }
type ('n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _model =
  { mutable i_139 : 'n ;
    mutable i_140 : 'm ;
    mutable major_99 : 'l ;
    mutable next_120 : 'k ;
    mutable h_119 : 'j ;
    mutable h_117 : 'i ;
    mutable i_115 : 'h ;
    mutable r_108 : 'g ;
    mutable s_107 : 'f ;
    mutable result_104 : 'e ;
    mutable zigzags_103 : 'd ;
    mutable fly_102 : 'c ; mutable car2_101 : 'b ; mutable car1_100 : 'a }

let model (cstate_143:Ztypes.cstate) = 
  let Node { alloc = i_139_alloc; step = i_139_step ; reset = i_139_reset } = print_status 
   in 
  let Node { alloc = i_140_alloc; step = i_140_step ; reset = i_140_reset } = print_status 
   in
  let model_alloc _ =
    cstate_143.cmax <- (+) cstate_143.cmax  3 ;
    cstate_143.zmax <- (+) cstate_143.zmax  1;
    { major_99 = false ;
      next_120 = { zin = false; zout = 1. } ;
      h_119 = 42. ;
      h_117 = (42.:float) ;
      i_115 = (false:bool) ;
      r_108 = (false:bool) ;
      s_107 = (Cantharide1_TowardBarcelona_56:state__944) ;
      result_104 = (42:int) ;
      zigzags_103 = (42:int) ;
      fly_102 = { pos = 42.; der = 0. } ;
      car2_101 = { pos = 42.; der = 0. } ; car1_100 = { pos = 42.; der = 0. };
      i_139 = i_139_alloc () (* discrete *)  ;
      i_140 = i_140_alloc () (* discrete *)  } in
  let model_step self ((time_98:float) , ()) =
    ((let (cindex_144:int) = cstate_143.cindex in
      let cpos_146 = ref (cindex_144:int) in
      let (zindex_145:int) = cstate_143.zindex in
      let zpos_147 = ref (zindex_145:int) in
      cstate_143.cindex <- (+) cstate_143.cindex  3 ;
      cstate_143.zindex <- (+) cstate_143.zindex  1 ;
      self.major_99 <- cstate_143.major ;
      (if cstate_143.major then
       for i_1 = cindex_144 to 2 do Zls.set cstate_143.dvec  i_1  0. done
       else ((self.fly_102.pos <- Zls.get cstate_143.cvec  !cpos_146 ;
              cpos_146 := (+) !cpos_146  1) ;
             (self.car2_101.pos <- Zls.get cstate_143.cvec  !cpos_146 ;
              cpos_146 := (+) !cpos_146  1) ;
             (self.car1_100.pos <- Zls.get cstate_143.cvec  !cpos_146 ;
              cpos_146 := (+) !cpos_146  1))) ;
      (let (result_148:(float  * float  * float  * int)) =
           let h_118 = ref (infinity:float) in
           let encore_116 = ref (false:bool) in
           let resultp_114 = ref (false:bool) in
           let resultv_113 = ref (():unit) in
           let zigp_112 = ref (false:bool) in
           let zigv_111 = ref (():unit) in
           let zagp_110 = ref (false:bool) in
           let zagv_109 = ref (():unit) in
           let (l_106:int) = self.result_104 in
           (if self.i_115 then self.car2_101.pos <- girona) ;
           (if self.i_115 then self.car1_100.pos <- barcelona) ;
           (begin match self.s_107 with
                  | Cantharide1_TowardGirona_55 ->
                      (if self.r_108 then ()) ;
                      self.fly_102.der <- fly_velocity ;
                      self.next_120.zout <- (-.) self.fly_102.pos 
                                                 self.car2_101.pos ;
                      (begin match self.next_120.zin with
                             | true ->
                                 encore_116 := true ;
                                 zagp_110 := true ;
                                 zagv_109 := () ;
                                 self.r_108 <- true ;
                                 self.s_107 <- Cantharide1_TowardBarcelona_56
                             | _ -> self.r_108 <- false  end)
                  | Cantharide1_TowardBarcelona_56 ->
                      (if self.r_108 then ()) ;
                      self.fly_102.der <- (~-.) fly_velocity ;
                      self.next_120.zout <- (-.) self.car1_100.pos 
                                                 self.fly_102.pos ;
                      (begin match self.next_120.zin with
                             | true ->
                                 encore_116 := true ;
                                 zigp_112 := true ;
                                 zigv_111 := () ;
                                 self.r_108 <- true ;
                                 self.s_107 <- Cantharide1_TowardGirona_55
                             | _ -> self.r_108 <- false  end)
                   end) ;
           (let (l_105:int) = self.zigzags_103 in
            (begin match ((!zagv_109 , !zagp_110) , (!zigv_111 , !zigp_112)) with
                   | (_ , (() , true)) ->
                       encore_116 := true ; self.result_104 <- (+) l_105  1
                   | ((() , true) , _) ->
                       encore_116 := true ; self.result_104 <- (+) l_105  1
                   | _ -> ()  end) ;
            self.h_117 <- (if !encore_116 then 0. else infinity) ;
            h_118 := min !h_118  self.h_117 ;
            self.h_119 <- !h_118 ;
            (if self.i_115 then self.fly_102.pos <- barcelona) ;
            self.i_115 <- false ;
            self.zigzags_103 <- self.result_104 ;
            (begin match ((!zagv_109 , !zagp_110) , (!zigv_111 , !zigp_112)) with
                   | (_ , (() , true)) ->
                       resultp_114 := true ;
                       resultv_113 := i_139_step self.i_139
                                        ("zig" ,
                                         self.car1_100.pos ,
                                         self.car2_101.pos ,
                                         self.fly_102.pos , self.zigzags_103)
                   | ((() , true) , _) ->
                       resultp_114 := true ;
                       resultv_113 := i_140_step self.i_140
                                        ("zag" ,
                                         self.car1_100.pos ,
                                         self.car2_101.pos ,
                                         self.fly_102.pos , self.zigzags_103)
                   | _ -> ()  end) ;
            (let _ = (!resultv_113 , !resultp_114) in
             self.car2_101.der <- (~-.) car_velocity ;
             self.car1_100.der <- car_velocity ;
             (self.car1_100.pos ,
              self.car2_101.pos , self.fly_102.pos , self.zigzags_103))) in
       cstate_143.horizon <- min cstate_143.horizon  self.h_119 ;
       cpos_146 := cindex_144 ;
       (if cstate_143.major then
        (((Zls.set cstate_143.cvec  !cpos_146  self.fly_102.pos ;
           cpos_146 := (+) !cpos_146  1) ;
          (Zls.set cstate_143.cvec  !cpos_146  self.car2_101.pos ;
           cpos_146 := (+) !cpos_146  1) ;
          (Zls.set cstate_143.cvec  !cpos_146  self.car1_100.pos ;
           cpos_146 := (+) !cpos_146  1)) ; ((self.next_120.zin <- false)))
        else (((self.next_120.zin <- Zls.get_zin cstate_143.zinvec  !zpos_147
                ; zpos_147 := (+) !zpos_147  1)) ;
              zpos_147 := zindex_145 ;
              ((Zls.set cstate_143.zoutvec  !zpos_147  self.next_120.zout ;
                zpos_147 := (+) !zpos_147  1)) ;
              ((Zls.set cstate_143.dvec  !cpos_146  self.fly_102.der ;
                cpos_146 := (+) !cpos_146  1) ;
               (Zls.set cstate_143.dvec  !cpos_146  self.car2_101.der ;
                cpos_146 := (+) !cpos_146  1) ;
               (Zls.set cstate_143.dvec  !cpos_146  self.car1_100.der ;
                cpos_146 := (+) !cpos_146  1)))) ; result_148)):float *
                                                                float *
                                                                float * int) in
  
  let model_reset self  =
    ((self.result_104 <- 0 ;
      self.r_108 <- false ;
      self.s_107 <- Cantharide1_TowardGirona_55 ;
      self.i_115 <- true ;
      self.zigzags_103 <- 0 ;
      i_139_reset self.i_139  ; i_140_reset self.i_140 ):unit) in
  Node { alloc = model_alloc; step = model_step ; reset = model_reset }
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_142 : 'l ;
    mutable i_141 : 'k ;
    mutable major_123 : 'j ;
    mutable next_134 : 'i ;
    mutable h_129 : 'h ;
    mutable h_127 : 'g ;
    mutable r_125 : 'f ;
    mutable s_124 : 'e ;
    mutable zigzags_133 : 'd ;
    mutable fly_132 : 'c ; mutable car2_131 : 'b ; mutable car1_130 : 'a }

let main (cstate_149:Ztypes.cstate) = 
  let Node { alloc = i_142_alloc; step = i_142_step ; reset = i_142_reset } = model 
  cstate_149 in 
  let Node { alloc = i_141_alloc; step = i_141_step ; reset = i_141_reset } = print_status 
   in
  let main_alloc _ =
    cstate_149.zmax <- (+) cstate_149.zmax  1;
    { major_123 = false ;
      next_134 = { zin = false; zout = 1. } ;
      h_129 = 42. ;
      h_127 = (42.:float) ;
      r_125 = (false:bool) ;
      s_124 = (Cantharide1_Finished_60:state__945) ;
      zigzags_133 = (42:int) ;
      fly_132 = (42.:float) ; car2_131 = (42.:float) ; car1_130 = (42.:float);
      i_142 = i_142_alloc () (* continuous *)  ;
      i_141 = i_141_alloc () (* discrete *)  } in
  let main_step self ((time_122:float) , ()) =
    ((let (zindex_151:int) = cstate_149.zindex in
      let zpos_153 = ref (zindex_151:int) in
      cstate_149.zindex <- (+) cstate_149.zindex  1 ;
      self.major_123 <- cstate_149.major ;
      (let (result_154:unit) =
           let h_128 = ref (infinity:float) in
           let encore_126 = ref (false:bool) in
           (begin match self.s_124 with
                  | Cantharide1_Running_59 ->
                      (if self.r_125 then
                       (i_142_reset self.i_142  ; i_141_reset self.i_141 )) ;
                      (let ((copy_135:float) ,
                            (copy_136:float) ,
                            (copy_137:float) , (copy_138:int)) =
                           i_142_step self.i_142 (time_122 , ()) in
                       self.car1_130 <- copy_135 ;
                       self.next_134.zout <- (-.) self.car1_130  girona ;
                       self.zigzags_133 <- copy_138 ;
                       self.fly_132 <- copy_137 ;
                       self.car2_131 <- copy_136 ;
                       (begin match self.next_134.zin with
                              | true ->
                                  encore_126 := true ;
                                  (let _ =
                                       i_141_step self.i_141
                                         ("done" ,
                                          self.car1_130 ,
                                          self.car2_131 ,
                                          self.fly_132 , self.zigzags_133) in
                                   self.r_125 <- true ;
                                   self.s_124 <- Cantharide1_Finished_60)
                              | _ -> self.r_125 <- false  end))
                  | Cantharide1_Finished_60 ->
                      (if self.r_125 then ()) ; self.r_125 <- false
                   end) ;
           self.h_127 <- (if !encore_126 then 0. else infinity) ;
           h_128 := min !h_128  self.h_127 ; self.h_129 <- !h_128 ; () in
       cstate_149.horizon <- min cstate_149.horizon  self.h_129 ;
       (if cstate_149.major then (((self.next_134.zin <- false)))
        else (((self.next_134.zin <- Zls.get_zin cstate_149.zinvec  !zpos_153
                ; zpos_153 := (+) !zpos_153  1)) ;
              zpos_153 := zindex_151 ;
              ((Zls.set cstate_149.zoutvec  !zpos_153  self.next_134.zout ;
                zpos_153 := (+) !zpos_153  1)))) ; result_154)):unit) in 
  let main_reset self  =
    ((self.r_125 <- false ;
      self.s_124 <- Cantharide1_Running_59 ;
      i_142_reset self.i_142  ; i_141_reset self.i_141 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
