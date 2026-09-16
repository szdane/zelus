(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type state__1163 = Cantharide3_Finished_87 | Cantharide3_Running_86 
type state__1162 = Cantharide3_Receding_83 | Cantharide3_Approaching_82 
type state__1161 =
Cantharide3_TowardBarcelona_74 | Cantharide3_TowardGirona_73 
let barcelona = 0.

let girona = 100.

let fly_velocity = 80.

let car_velocity = 50.

type _print_status = unit

let print_status  = 
   let print_status_alloc _ = () in
  let print_status_reset self  =
    ((()):unit) in 
  let print_status_step self ((eventname_135:string) ,
                              (car1_133:float) ,
                              (car2_134:float) ,
                              (fly_136:float) , (zigzags_137:int)) =
    ((let _ = flush stdout in
      print_endline ((^) eventname_135 
                         ((^) ": car1=" 
                              ((^) (string_of_float car1_133) 
                                   ((^) "; car2=" 
                                        ((^) (string_of_float car2_134) 
                                             ((^) "; fly=" 
                                                  ((^) (string_of_float 
                                                          fly_136) 
                                                       ((^) "; zigzags=" 
                                                            (string_of_float 
                                                               ((/.) 
                                                                  (float 
                                                                    zigzags_137)
                                                                   2.))))))))))):
    unit) in
  Node { alloc = print_status_alloc; reset = print_status_reset ;
                                     step = print_status_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _zigzagfly =
  { mutable major_142 : 'g ;
    mutable next_154 : 'f ;
    mutable h_153 : 'e ;
    mutable h_151 : 'd ;
    mutable r_145 : 'c ; mutable s_144 : 'b ; mutable velocity_143 : 'a }

let zigzagfly (cstate_213:Ztypes.cstate) = 
  
  let zigzagfly_alloc _ =
    cstate_213.zmax <- (+) cstate_213.zmax  1;
    { major_142 = false ;
      next_154 = { zin = false; zout = 1. } ;
      h_153 = 42. ;
      h_151 = (42.:float) ;
      r_145 = (false:bool) ;
      s_144 = (Cantharide3_TowardBarcelona_74:state__1161) ;
      velocity_143 = (42.:float) } in
  let zigzagfly_step self ((time_141:float) ,
                           ((car1_138:float) ,
                            (car2_139:float) , (fly_140:float))) =
    ((let (zindex_215:int) = cstate_213.zindex in
      let zpos_217 = ref (zindex_215:int) in
      cstate_213.zindex <- (+) cstate_213.zindex  1 ;
      self.major_142 <- cstate_213.major ;
      (let (result_218:(float  * (unit)signal  * (unit)signal)) =
           let h_152 = ref (infinity:float) in
           let encore_150 = ref (false:bool) in
           let zigp_149 = ref (false:bool) in
           let zigv_148 = ref (():unit) in
           let zagp_147 = ref (false:bool) in
           let zagv_146 = ref (():unit) in
           (begin match self.s_144 with
                  | Cantharide3_TowardGirona_73 ->
                      (if self.r_145 then ()) ;
                      self.velocity_143 <- fly_velocity ;
                      self.next_154.zout <- (-.) fly_140  car2_139 ;
                      (begin match self.next_154.zin with
                             | true ->
                                 encore_150 := true ;
                                 zagp_147 := true ;
                                 zagv_146 := () ;
                                 self.r_145 <- true ;
                                 self.s_144 <- Cantharide3_TowardBarcelona_74
                             | _ -> self.r_145 <- false  end)
                  | Cantharide3_TowardBarcelona_74 ->
                      (if self.r_145 then ()) ;
                      self.velocity_143 <- (~-.) fly_velocity ;
                      self.next_154.zout <- (-.) car1_138  fly_140 ;
                      (begin match self.next_154.zin with
                             | true ->
                                 encore_150 := true ;
                                 zigp_149 := true ;
                                 zigv_148 := () ;
                                 self.r_145 <- true ;
                                 self.s_144 <- Cantharide3_TowardGirona_73
                             | _ -> self.r_145 <- false  end)
                   end) ;
           self.h_151 <- (if !encore_150 then 0. else infinity) ;
           h_152 := min !h_152  self.h_151 ;
           self.h_153 <- !h_152 ;
           (self.velocity_143 ,
            (!zigv_148 , !zigp_149) , (!zagv_146 , !zagp_147)) in
       cstate_213.horizon <- min cstate_213.horizon  self.h_153 ;
       (if cstate_213.major then (((self.next_154.zin <- false)))
        else (((self.next_154.zin <- Zls.get_zin cstate_213.zinvec  !zpos_217
                ; zpos_217 := (+) !zpos_217  1)) ;
              zpos_217 := zindex_215 ;
              ((Zls.set cstate_213.zoutvec  !zpos_217  self.next_154.zout ;
                zpos_217 := (+) !zpos_217  1)))) ; result_218)):float *
                                                                unit signal *
                                                                unit signal) in
  
  let zigzagfly_reset self  =
    ((self.r_145 <- false ; self.s_144 <- Cantharide3_TowardGirona_73):
    unit) in
  Node { alloc = zigzagfly_alloc; step = zigzagfly_step ;
                                  reset = zigzagfly_reset }
type ('q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _model =
  { mutable i_209 : 'q ;
    mutable i_210 : 'p ;
    mutable i_207 : 'o ;
    mutable i_208 : 'n ;
    mutable major_157 : 'm ;
    mutable next_179 : 'l ;
    mutable h_178 : 'k ;
    mutable h_176 : 'j ;
    mutable i_174 : 'i ;
    mutable r_167 : 'h ;
    mutable s_166 : 'g ;
    mutable result_163 : 'f ;
    mutable zigzags_162 : 'e ;
    mutable fly_velocity_161 : 'd ;
    mutable fly_160 : 'c ; mutable car2_159 : 'b ; mutable car1_158 : 'a }

let model (cstate_219:Ztypes.cstate) = 
  let Node { alloc = i_209_alloc; step = i_209_step ; reset = i_209_reset } = zigzagfly 
  cstate_219 in 
  let Node { alloc = i_210_alloc; step = i_210_step ; reset = i_210_reset } = zigzagfly 
  cstate_219 in 
  let Node { alloc = i_207_alloc; step = i_207_step ; reset = i_207_reset } = print_status 
   in 
  let Node { alloc = i_208_alloc; step = i_208_step ; reset = i_208_reset } = print_status 
   in
  let model_alloc _ =
    cstate_219.cmax <- (+) cstate_219.cmax  3 ;
    cstate_219.zmax <- (+) cstate_219.zmax  1;
    { major_157 = false ;
      next_179 = { zin = false; zout = 1. } ;
      h_178 = 42. ;
      h_176 = (42.:float) ;
      i_174 = (false:bool) ;
      r_167 = (false:bool) ;
      s_166 = (Cantharide3_Receding_83:state__1162) ;
      result_163 = (42:int) ;
      zigzags_162 = (42:int) ;
      fly_velocity_161 = (42.:float) ;
      fly_160 = { pos = 42.; der = 0. } ;
      car2_159 = { pos = 42.; der = 0. } ; car1_158 = { pos = 42.; der = 0. };
      i_209 = i_209_alloc () (* continuous *)  ;
      i_210 = i_210_alloc () (* continuous *)  ;
      i_207 = i_207_alloc () (* discrete *)  ;
      i_208 = i_208_alloc () (* discrete *)  } in
  let model_step self ((time_156:float) , ()) =
    ((let (cindex_220:int) = cstate_219.cindex in
      let cpos_222 = ref (cindex_220:int) in
      let (zindex_221:int) = cstate_219.zindex in
      let zpos_223 = ref (zindex_221:int) in
      cstate_219.cindex <- (+) cstate_219.cindex  3 ;
      cstate_219.zindex <- (+) cstate_219.zindex  1 ;
      self.major_157 <- cstate_219.major ;
      (if cstate_219.major then
       for i_1 = cindex_220 to 2 do Zls.set cstate_219.dvec  i_1  0. done
       else ((self.fly_160.pos <- Zls.get cstate_219.cvec  !cpos_222 ;
              cpos_222 := (+) !cpos_222  1) ;
             (self.car2_159.pos <- Zls.get cstate_219.cvec  !cpos_222 ;
              cpos_222 := (+) !cpos_222  1) ;
             (self.car1_158.pos <- Zls.get cstate_219.cvec  !cpos_222 ;
              cpos_222 := (+) !cpos_222  1))) ;
      (let (result_224:(float  * float  * float  * int)) =
           let h_177 = ref (infinity:float) in
           let encore_175 = ref (false:bool) in
           let resultp_173 = ref (false:bool) in
           let resultv_172 = ref (():unit) in
           let zigp_171 = ref (false:bool) in
           let zigv_170 = ref (():unit) in
           let zagp_169 = ref (false:bool) in
           let zagv_168 = ref (():unit) in
           let (l_165:int) = self.result_163 in
           (if self.i_174 then self.fly_160.pos <- barcelona) ;
           (if self.i_174 then self.car2_159.pos <- girona) ;
           (if self.i_174 then self.car1_158.pos <- barcelona) ;
           (begin match self.s_166 with
                  | Cantharide3_Approaching_82 ->
                      (if self.r_167 then i_209_reset self.i_209 ) ;
                      (let ((copy_193:float) ,
                            ((copy_194:unit) , (copy_195:bool)) ,
                            ((copy_196:unit) , (copy_197:bool))) =
                           i_209_step self.i_209
                             (time_156 ,
                              (self.car1_158.pos ,
                               self.car2_159.pos , self.fly_160.pos)) in
                       zigp_171 := copy_195 ;
                       zigv_170 := copy_194 ;
                       zagp_169 := copy_197 ;
                       zagv_168 := copy_196 ;
                       self.fly_velocity_161 <- copy_193 ;
                       self.next_179.zout <- (-.) self.car1_158.pos 
                                                  self.car2_159.pos ;
                       (begin match self.next_179.zin with
                              | true ->
                                  encore_175 := true ;
                                  self.r_167 <- true ;
                                  self.s_166 <- Cantharide3_Receding_83
                              | _ -> self.r_167 <- false  end))
                  | Cantharide3_Receding_83 ->
                      (if self.r_167 then i_210_reset self.i_210 ) ;
                      (let ((copy_198:float) ,
                            ((copy_199:unit) , (copy_200:bool)) ,
                            ((copy_201:unit) , (copy_202:bool))) =
                           i_210_step self.i_210
                             (time_156 ,
                              (self.car2_159.pos ,
                               self.car1_158.pos , self.fly_160.pos)) in
                       zigp_171 := copy_200 ;
                       zigv_170 := copy_199 ;
                       zagp_169 := copy_202 ;
                       zagv_168 := copy_201 ;
                       self.fly_velocity_161 <- copy_198 ;
                       self.r_167 <- false)
                   end) ;
           (let (l_164:int) = self.zigzags_162 in
            (begin match ((!zagv_168 , !zagp_169) , (!zigv_170 , !zigp_171)) with
                   | (_ , (() , true)) ->
                       encore_175 := true ; self.result_163 <- (+) l_164  1
                   | ((() , true) , _) ->
                       encore_175 := true ; self.result_163 <- (+) l_164  1
                   | _ -> ()  end) ;
            self.h_176 <- (if !encore_175 then 0. else infinity) ;
            h_177 := min !h_177  self.h_176 ;
            self.h_178 <- !h_177 ;
            self.i_174 <- false ;
            self.zigzags_162 <- self.result_163 ;
            (begin match ((!zagv_168 , !zagp_169) , (!zigv_170 , !zigp_171)) with
                   | (_ , (() , true)) ->
                       resultp_173 := true ;
                       resultv_172 := i_207_step self.i_207
                                        ("zig" ,
                                         self.car1_158.pos ,
                                         self.car2_159.pos ,
                                         self.fly_160.pos , self.zigzags_162)
                   | ((() , true) , _) ->
                       resultp_173 := true ;
                       resultv_172 := i_208_step self.i_208
                                        ("zag" ,
                                         self.car1_158.pos ,
                                         self.car2_159.pos ,
                                         self.fly_160.pos , self.zigzags_162)
                   | _ -> ()  end) ;
            (let _ = (!resultv_172 , !resultp_173) in
             self.fly_160.der <- self.fly_velocity_161 ;
             self.car2_159.der <- (~-.) car_velocity ;
             self.car1_158.der <- car_velocity ;
             (self.car1_158.pos ,
              self.car2_159.pos , self.fly_160.pos , self.zigzags_162))) in
       cstate_219.horizon <- min cstate_219.horizon  self.h_178 ;
       cpos_222 := cindex_220 ;
       (if cstate_219.major then
        (((Zls.set cstate_219.cvec  !cpos_222  self.fly_160.pos ;
           cpos_222 := (+) !cpos_222  1) ;
          (Zls.set cstate_219.cvec  !cpos_222  self.car2_159.pos ;
           cpos_222 := (+) !cpos_222  1) ;
          (Zls.set cstate_219.cvec  !cpos_222  self.car1_158.pos ;
           cpos_222 := (+) !cpos_222  1)) ; ((self.next_179.zin <- false)))
        else (((self.next_179.zin <- Zls.get_zin cstate_219.zinvec  !zpos_223
                ; zpos_223 := (+) !zpos_223  1)) ;
              zpos_223 := zindex_221 ;
              ((Zls.set cstate_219.zoutvec  !zpos_223  self.next_179.zout ;
                zpos_223 := (+) !zpos_223  1)) ;
              ((Zls.set cstate_219.dvec  !cpos_222  self.fly_160.der ;
                cpos_222 := (+) !cpos_222  1) ;
               (Zls.set cstate_219.dvec  !cpos_222  self.car2_159.der ;
                cpos_222 := (+) !cpos_222  1) ;
               (Zls.set cstate_219.dvec  !cpos_222  self.car1_158.der ;
                cpos_222 := (+) !cpos_222  1)))) ; result_224)):float *
                                                                float *
                                                                float * int) in
  
  let model_reset self  =
    ((self.result_163 <- 0 ;
      self.r_167 <- false ;
      self.s_166 <- Cantharide3_Approaching_82 ;
      self.i_174 <- true ;
      i_209_reset self.i_209  ;
      i_210_reset self.i_210  ;
      self.zigzags_162 <- 0 ;
      i_207_reset self.i_207  ; i_208_reset self.i_208 ):unit) in
  Node { alloc = model_alloc; step = model_step ; reset = model_reset }
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_212 : 'l ;
    mutable i_211 : 'k ;
    mutable major_181 : 'j ;
    mutable next_192 : 'i ;
    mutable h_187 : 'h ;
    mutable h_185 : 'g ;
    mutable r_183 : 'f ;
    mutable s_182 : 'e ;
    mutable zigzags_191 : 'd ;
    mutable fly_190 : 'c ; mutable car2_189 : 'b ; mutable car1_188 : 'a }

let main (cstate_225:Ztypes.cstate) = 
  let Node { alloc = i_212_alloc; step = i_212_step ; reset = i_212_reset } = model 
  cstate_225 in 
  let Node { alloc = i_211_alloc; step = i_211_step ; reset = i_211_reset } = print_status 
   in
  let main_alloc _ =
    cstate_225.zmax <- (+) cstate_225.zmax  1;
    { major_181 = false ;
      next_192 = { zin = false; zout = 1. } ;
      h_187 = 42. ;
      h_185 = (42.:float) ;
      r_183 = (false:bool) ;
      s_182 = (Cantharide3_Finished_87:state__1163) ;
      zigzags_191 = (42:int) ;
      fly_190 = (42.:float) ; car2_189 = (42.:float) ; car1_188 = (42.:float);
      i_212 = i_212_alloc () (* continuous *)  ;
      i_211 = i_211_alloc () (* discrete *)  } in
  let main_step self ((time_180:float) , ()) =
    ((let (zindex_227:int) = cstate_225.zindex in
      let zpos_229 = ref (zindex_227:int) in
      cstate_225.zindex <- (+) cstate_225.zindex  1 ;
      self.major_181 <- cstate_225.major ;
      (let (result_230:unit) =
           let h_186 = ref (infinity:float) in
           let encore_184 = ref (false:bool) in
           (begin match self.s_182 with
                  | Cantharide3_Running_86 ->
                      (if self.r_183 then
                       (i_212_reset self.i_212  ; i_211_reset self.i_211 )) ;
                      (let ((copy_203:float) ,
                            (copy_204:float) ,
                            (copy_205:float) , (copy_206:int)) =
                           i_212_step self.i_212 (time_180 , ()) in
                       self.car1_188 <- copy_203 ;
                       self.next_192.zout <- (-.) self.car1_188  girona ;
                       self.zigzags_191 <- copy_206 ;
                       self.fly_190 <- copy_205 ;
                       self.car2_189 <- copy_204 ;
                       (begin match self.next_192.zin with
                              | true ->
                                  encore_184 := true ;
                                  (let () =
                                       i_211_step self.i_211
                                         ("done" ,
                                          self.car1_188 ,
                                          self.car2_189 ,
                                          self.fly_190 , self.zigzags_191) in
                                   self.r_183 <- true ;
                                   self.s_182 <- Cantharide3_Finished_87)
                              | _ -> self.r_183 <- false  end))
                  | Cantharide3_Finished_87 ->
                      (if self.r_183 then ()) ; self.r_183 <- false
                   end) ;
           self.h_185 <- (if !encore_184 then 0. else infinity) ;
           h_186 := min !h_186  self.h_185 ; self.h_187 <- !h_186 ; () in
       cstate_225.horizon <- min cstate_225.horizon  self.h_187 ;
       (if cstate_225.major then (((self.next_192.zin <- false)))
        else (((self.next_192.zin <- Zls.get_zin cstate_225.zinvec  !zpos_229
                ; zpos_229 := (+) !zpos_229  1)) ;
              zpos_229 := zindex_227 ;
              ((Zls.set cstate_225.zoutvec  !zpos_229  self.next_192.zout ;
                zpos_229 := (+) !zpos_229  1)))) ; result_230)):unit) in 
  let main_reset self  =
    ((self.r_183 <- false ;
      self.s_182 <- Cantharide3_Running_86 ;
      i_212_reset self.i_212  ; i_211_reset self.i_211 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
