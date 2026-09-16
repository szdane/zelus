(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type state__1077 = Cantharide2_Finished_63 | Cantharide2_Running_62 
type state__1076 =
Cantharide2_TowardBarcelona_59 | Cantharide2_TowardGirona_58 
let barcelona = 0.

let girona = 100.

let fly_velocity = 80.

let car_velocity = 50.

type _print_status = unit

let print_status  = 
   let print_status_alloc _ = () in
  let print_status_reset self  =
    ((()):unit) in 
  let print_status_step self ((eventname_101:string) ,
                              (car1_99:float) ,
                              (car2_100:float) ,
                              (fly_102:float) , (zigzags_103:int)) =
    ((let _ = flush stdout in
      print_endline ((^) eventname_101 
                         ((^) ": car1=" 
                              ((^) (string_of_float car1_99) 
                                   ((^) "; car2=" 
                                        ((^) (string_of_float car2_100) 
                                             ((^) "; fly=" 
                                                  ((^) (string_of_float 
                                                          fly_102) 
                                                       ((^) "; zigzags=" 
                                                            (string_of_float 
                                                               ((/.) 
                                                                  (float 
                                                                    zigzags_103)
                                                                   2.))))))))))):
    unit) in
  Node { alloc = print_status_alloc; reset = print_status_reset ;
                                     step = print_status_step }
type ('p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _model =
  { mutable i_149 : 'p ;
    mutable i_150 : 'o ;
    mutable major_105 : 'n ;
    mutable next_129 : 'm ;
    mutable next_128 : 'l ;
    mutable h_127 : 'k ;
    mutable h_125 : 'j ;
    mutable i_123 : 'i ;
    mutable r_116 : 'h ;
    mutable s_115 : 'g ;
    mutable result_111 : 'f ;
    mutable zigzags_110 : 'e ;
    mutable velocity_109 : 'd ;
    mutable fly_108 : 'c ; mutable car2_107 : 'b ; mutable car1_106 : 'a }

let model (cstate_153:Ztypes.cstate) = 
  let Node { alloc = i_149_alloc; step = i_149_step ; reset = i_149_reset } = print_status 
   in 
  let Node { alloc = i_150_alloc; step = i_150_step ; reset = i_150_reset } = print_status 
   in
  let model_alloc _ =
    cstate_153.cmax <- (+) cstate_153.cmax  3 ;
    cstate_153.zmax <- (+) cstate_153.zmax  2;
    { major_105 = false ;
      next_129 = { zin = false; zout = 1. } ;
      next_128 = { zin = false; zout = 1. } ;
      h_127 = 42. ;
      h_125 = (42.:float) ;
      i_123 = (false:bool) ;
      r_116 = (false:bool) ;
      s_115 = (Cantharide2_TowardBarcelona_59:state__1076) ;
      result_111 = (42:int) ;
      zigzags_110 = (42:int) ;
      velocity_109 = (42.:float) ;
      fly_108 = { pos = 42.; der = 0. } ;
      car2_107 = { pos = 42.; der = 0. } ; car1_106 = { pos = 42.; der = 0. };
      i_149 = i_149_alloc () (* discrete *)  ;
      i_150 = i_150_alloc () (* discrete *)  } in
  let model_step self ((time_104:float) , ()) =
    ((let (cindex_154:int) = cstate_153.cindex in
      let cpos_156 = ref (cindex_154:int) in
      let (zindex_155:int) = cstate_153.zindex in
      let zpos_157 = ref (zindex_155:int) in
      cstate_153.cindex <- (+) cstate_153.cindex  3 ;
      cstate_153.zindex <- (+) cstate_153.zindex  2 ;
      self.major_105 <- cstate_153.major ;
      (if cstate_153.major then
       for i_1 = cindex_154 to 2 do Zls.set cstate_153.dvec  i_1  0. done
       else ((self.fly_108.pos <- Zls.get cstate_153.cvec  !cpos_156 ;
              cpos_156 := (+) !cpos_156  1) ;
             (self.car2_107.pos <- Zls.get cstate_153.cvec  !cpos_156 ;
              cpos_156 := (+) !cpos_156  1) ;
             (self.car1_106.pos <- Zls.get cstate_153.cvec  !cpos_156 ;
              cpos_156 := (+) !cpos_156  1))) ;
      (let (result_158:(float  * float  * float  * int)) =
           let h_126 = ref (infinity:float) in
           let encore_124 = ref (false:bool) in
           let resultp_122 = ref (false:bool) in
           let resultv_121 = ref (():unit) in
           let zigp_120 = ref (false:bool) in
           let zigv_119 = ref (():unit) in
           let zagp_118 = ref (false:bool) in
           let zagv_117 = ref (():unit) in
           let (l_114:int) = self.result_111 in
           (if self.i_123 then self.car2_107.pos <- girona) ;
           (if self.i_123 then self.car1_106.pos <- barcelona) ;
           (if self.i_123 then self.fly_108.pos <- barcelona) ;
           (let (l_112:float) = self.fly_108.pos in
            (begin match self.s_115 with
                   | Cantharide2_TowardGirona_58 ->
                       (if self.r_116 then ()) ;
                       self.velocity_109 <- fly_velocity ;
                       self.next_129.zout <- (-.) l_112  self.car2_107.pos ;
                       self.next_128.zout <- (-.) l_112  self.car1_106.pos ;
                       (begin match (self.next_128.zin , self.next_129.zin) with
                              | (_ , true) ->
                                  encore_124 := true ;
                                  zagp_118 := true ;
                                  zagv_117 := () ;
                                  self.r_116 <- true ;
                                  self.s_115 <- Cantharide2_TowardBarcelona_59
                              | (true , _) ->
                                  encore_124 := true ;
                                  zigp_120 := true ;
                                  zigv_119 := () ;
                                  self.r_116 <- true ;
                                  self.s_115 <- Cantharide2_TowardBarcelona_59
                              | _ -> self.r_116 <- false  end)
                   | Cantharide2_TowardBarcelona_59 ->
                       (if self.r_116 then ()) ;
                       self.velocity_109 <- (~-.) fly_velocity ;
                       self.next_129.zout <- (-.) self.car1_106.pos  l_112 ;
                       self.next_128.zout <- (-.) self.car2_107.pos  l_112 ;
                       (begin match (self.next_128.zin , self.next_129.zin) with
                              | (_ , true) ->
                                  encore_124 := true ;
                                  zigp_120 := true ;
                                  zigv_119 := () ;
                                  self.r_116 <- true ;
                                  self.s_115 <- Cantharide2_TowardGirona_58
                              | (true , _) ->
                                  encore_124 := true ;
                                  zagp_118 := true ;
                                  zagv_117 := () ;
                                  self.r_116 <- true ;
                                  self.s_115 <- Cantharide2_TowardGirona_58
                              | _ -> self.r_116 <- false  end)
                    end) ;
            (let (l_113:int) = self.zigzags_110 in
             (begin match ((!zagv_117 , !zagp_118) , (!zigv_119 , !zigp_120)) with
                    | (_ , (() , true)) ->
                        encore_124 := true ; self.result_111 <- (+) l_113  1
                    | ((() , true) , _) ->
                        encore_124 := true ; self.result_111 <- (+) l_113  1
                    | _ -> ()  end) ;
             (begin match ((!zigv_119 , !zigp_120) , (!zagv_117 , !zagp_118)) with
                    | (_ , (() , true)) ->
                        encore_124 := true ;
                        self.fly_108.pos <- self.car2_107.pos
                    | ((() , true) , _) ->
                        encore_124 := true ;
                        self.fly_108.pos <- self.car1_106.pos
                    | _ -> ()  end) ;
             self.h_125 <- (if !encore_124 then 0. else infinity) ;
             h_126 := min !h_126  self.h_125 ;
             self.h_127 <- !h_126 ;
             self.i_123 <- false ;
             self.zigzags_110 <- self.result_111 ;
             (begin match ((!zagv_117 , !zagp_118) , (!zigv_119 , !zigp_120)) with
                    | (_ , (() , true)) ->
                        resultp_122 := true ;
                        resultv_121 := i_149_step self.i_149
                                         ("zig" ,
                                          self.car1_106.pos ,
                                          self.car2_107.pos ,
                                          self.fly_108.pos , self.zigzags_110)
                    | ((() , true) , _) ->
                        resultp_122 := true ;
                        resultv_121 := i_150_step self.i_150
                                         ("zag" ,
                                          self.car1_106.pos ,
                                          self.car2_107.pos ,
                                          self.fly_108.pos , self.zigzags_110)
                    | _ -> ()  end) ;
             (let _ = (!resultv_121 , !resultp_122) in
              self.fly_108.der <- self.velocity_109 ;
              self.car2_107.der <- (~-.) car_velocity ;
              self.car1_106.der <- car_velocity ;
              (self.car1_106.pos ,
               self.car2_107.pos , self.fly_108.pos , self.zigzags_110)))) in
       cstate_153.horizon <- min cstate_153.horizon  self.h_127 ;
       cpos_156 := cindex_154 ;
       (if cstate_153.major then
        (((Zls.set cstate_153.cvec  !cpos_156  self.fly_108.pos ;
           cpos_156 := (+) !cpos_156  1) ;
          (Zls.set cstate_153.cvec  !cpos_156  self.car2_107.pos ;
           cpos_156 := (+) !cpos_156  1) ;
          (Zls.set cstate_153.cvec  !cpos_156  self.car1_106.pos ;
           cpos_156 := (+) !cpos_156  1)) ;
         ((self.next_129.zin <- false) ; (self.next_128.zin <- false)))
        else (((self.next_129.zin <- Zls.get_zin cstate_153.zinvec  !zpos_157
                ; zpos_157 := (+) !zpos_157  1) ;
               (self.next_128.zin <- Zls.get_zin cstate_153.zinvec  !zpos_157
                ; zpos_157 := (+) !zpos_157  1)) ;
              zpos_157 := zindex_155 ;
              ((Zls.set cstate_153.zoutvec  !zpos_157  self.next_129.zout ;
                zpos_157 := (+) !zpos_157  1) ;
               (Zls.set cstate_153.zoutvec  !zpos_157  self.next_128.zout ;
                zpos_157 := (+) !zpos_157  1)) ;
              ((Zls.set cstate_153.dvec  !cpos_156  self.fly_108.der ;
                cpos_156 := (+) !cpos_156  1) ;
               (Zls.set cstate_153.dvec  !cpos_156  self.car2_107.der ;
                cpos_156 := (+) !cpos_156  1) ;
               (Zls.set cstate_153.dvec  !cpos_156  self.car1_106.der ;
                cpos_156 := (+) !cpos_156  1)))) ; result_158)):float *
                                                                float *
                                                                float * int) in
  
  let model_reset self  =
    ((self.result_111 <- 0 ;
      self.r_116 <- false ;
      self.s_115 <- Cantharide2_TowardGirona_58 ;
      self.i_123 <- true ;
      self.zigzags_110 <- 0 ;
      i_149_reset self.i_149  ; i_150_reset self.i_150 ):unit) in
  Node { alloc = model_alloc; step = model_step ; reset = model_reset }
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_152 : 'l ;
    mutable i_151 : 'k ;
    mutable major_133 : 'j ;
    mutable next_144 : 'i ;
    mutable h_139 : 'h ;
    mutable h_137 : 'g ;
    mutable r_135 : 'f ;
    mutable s_134 : 'e ;
    mutable zigzags_143 : 'd ;
    mutable fly_142 : 'c ; mutable car2_141 : 'b ; mutable car1_140 : 'a }

let main (cstate_159:Ztypes.cstate) = 
  let Node { alloc = i_152_alloc; step = i_152_step ; reset = i_152_reset } = model 
  cstate_159 in 
  let Node { alloc = i_151_alloc; step = i_151_step ; reset = i_151_reset } = print_status 
   in
  let main_alloc _ =
    cstate_159.zmax <- (+) cstate_159.zmax  1;
    { major_133 = false ;
      next_144 = { zin = false; zout = 1. } ;
      h_139 = 42. ;
      h_137 = (42.:float) ;
      r_135 = (false:bool) ;
      s_134 = (Cantharide2_Finished_63:state__1077) ;
      zigzags_143 = (42:int) ;
      fly_142 = (42.:float) ; car2_141 = (42.:float) ; car1_140 = (42.:float);
      i_152 = i_152_alloc () (* continuous *)  ;
      i_151 = i_151_alloc () (* discrete *)  } in
  let main_step self ((time_132:float) , ()) =
    ((let (zindex_161:int) = cstate_159.zindex in
      let zpos_163 = ref (zindex_161:int) in
      cstate_159.zindex <- (+) cstate_159.zindex  1 ;
      self.major_133 <- cstate_159.major ;
      (let (result_164:unit) =
           let h_138 = ref (infinity:float) in
           let encore_136 = ref (false:bool) in
           (begin match self.s_134 with
                  | Cantharide2_Running_62 ->
                      (if self.r_135 then
                       (i_152_reset self.i_152  ; i_151_reset self.i_151 )) ;
                      (let ((copy_145:float) ,
                            (copy_146:float) ,
                            (copy_147:float) , (copy_148:int)) =
                           i_152_step self.i_152 (time_132 , ()) in
                       self.car1_140 <- copy_145 ;
                       self.next_144.zout <- (-.) self.car1_140  girona ;
                       self.zigzags_143 <- copy_148 ;
                       self.fly_142 <- copy_147 ;
                       self.car2_141 <- copy_146 ;
                       (begin match self.next_144.zin with
                              | true ->
                                  encore_136 := true ;
                                  (let () =
                                       i_151_step self.i_151
                                         ("done" ,
                                          self.car1_140 ,
                                          self.car2_141 ,
                                          self.fly_142 , self.zigzags_143) in
                                   self.r_135 <- true ;
                                   self.s_134 <- Cantharide2_Finished_63)
                              | _ -> self.r_135 <- false  end))
                  | Cantharide2_Finished_63 ->
                      (if self.r_135 then ()) ; self.r_135 <- false
                   end) ;
           self.h_137 <- (if !encore_136 then 0. else infinity) ;
           h_138 := min !h_138  self.h_137 ; self.h_139 <- !h_138 ; () in
       cstate_159.horizon <- min cstate_159.horizon  self.h_139 ;
       (if cstate_159.major then (((self.next_144.zin <- false)))
        else (((self.next_144.zin <- Zls.get_zin cstate_159.zinvec  !zpos_163
                ; zpos_163 := (+) !zpos_163  1)) ;
              zpos_163 := zindex_161 ;
              ((Zls.set cstate_159.zoutvec  !zpos_163  self.next_144.zout ;
                zpos_163 := (+) !zpos_163  1)))) ; result_164)):unit) in 
  let main_reset self  =
    ((self.r_135 <- false ;
      self.s_134 <- Cantharide2_Running_62 ;
      i_152_reset self.i_152  ; i_151_reset self.i_151 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
