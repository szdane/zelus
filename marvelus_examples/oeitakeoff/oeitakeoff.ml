(* The Zelus compiler, version 2.2-dev
  (2026-03-30-22:46) *)
open Ztypes
type state__3345 =
Oeitakeoff_ClimbOEI_94
| Oeitakeoff_OEIOnGround_93
| Oeitakeoff_TakeoffAfterDecisionSpeed_92
| Oeitakeoff_StopFully_91
| Oeitakeoff_Stop_90 | Oeitakeoff_TakeoffBeforeDecisionSpeed_89 
type state__3344 =
Oeitakeoff_ClimbOEI_68
| Oeitakeoff_OEIOnGround_67
| Oeitakeoff_TakeoffAfterDecisionSpeed_66
| Oeitakeoff_StopFully_65
| Oeitakeoff_Stop_64 | Oeitakeoff_TakeoffBeforeDecisionSpeed_63 
let xinit = 0.

let vinit = 0.

let hinit = 0.

let a = 2.

let dt = 0.1

let coei = 2.

let c = 4.

let vstallflaps = 20.

let vstallclean = 25.

let b = 5.

let oeicruise = 1500.

let hceiling = 23000.

let vdecision = 20.17

let xoei = 1000.

let xc = 300.

let lrunway = 118.292775

type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _takeoff =
  { mutable i_128 : 'l ;
    mutable r_127 : 'k ;
    mutable s_126 : 'j ;
    mutable x_122 : 'i ;
    mutable ww_121 : 'h ;
    mutable vel_120 : 'g ;
    mutable thr_119 : 'f ;
    mutable oei_118 : 'e ;
    mutable obsclear_117 : 'd ;
    mutable lg_116 : 'c ; mutable h_115 : 'b ; mutable fl_114 : 'a }

let takeoff  = 
  
  let takeoff_alloc _ =
    ();
    { i_128 = (false:bool) ;
      r_127 = (false:bool) ;
      s_126 = (Oeitakeoff_ClimbOEI_68:state__3344) ;
      x_122 = (42.:float) ;
      ww_121 = (false:bool) ;
      vel_120 = (42.:float) ;
      thr_119 = (false:bool) ;
      oei_118 = (false:bool) ;
      obsclear_117 = (false:bool) ;
      lg_116 = (false:bool) ; h_115 = (42.:float) ; fl_114 = (false:bool) } in
  let takeoff_reset self  =
    ((self.i_128 <- true ;
      self.r_127 <- false ;
      self.s_126 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_63 ;
      self.obsclear_117 <- false ;
      self.oei_118 <- false ;
      self.ww_121 <- true ;
      self.lg_116 <- true ; self.fl_114 <- true ; self.thr_119 <- true):
    unit) in 
  let takeoff_step self () =
    (((if self.i_128 then self.vel_120 <- vinit) ;
      (if self.i_128 then self.h_115 <- hinit) ;
      (if self.i_128 then self.x_122 <- xinit) ;
      self.i_128 <- false ;
      (let (l_124:float) = self.vel_120 in
       let (l_125:float) = self.x_122 in
       (begin match self.s_126 with
              | Oeitakeoff_TakeoffBeforeDecisionSpeed_63 ->
                  (if self.r_127 then ()) ;
                  (begin match (((>=) l_125 
                                      ((-.) xoei 
                                            ((+.) (( *. ) l_124  dt) 
                                                  (( *. ) (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)  
                                                          dt)))) ,
                                ((>) l_124  ((-.) vdecision  (( *. ) a  dt)))) with
                         | (_ , true) ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_TakeoffAfterDecisionSpeed_66
                         | (true , _) ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_Stop_64
                         | _ -> self.r_127 <- false  end)
              | Oeitakeoff_Stop_64 ->
                  (if self.r_127 then ()) ;
                  (begin match (<=) l_124  ((+.) 0.  (( *. ) b  dt)) with
                         | true ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_StopFully_65
                         | _ -> self.r_127 <- false  end)
              | Oeitakeoff_StopFully_65 ->
                  (if self.r_127 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_StopFully_65
                         | _ -> self.r_127 <- false  end)
              | Oeitakeoff_TakeoffAfterDecisionSpeed_66 ->
                  (if self.r_127 then ()) ;
                  (begin match (>=) l_125 
                                    ((-.) xoei 
                                          ((+.) (( *. ) l_124  dt) 
                                                (( *. ) (( *. ) (( *. ) 
                                                                   0.5  a) 
                                                                dt)  
                                                        dt))) with
                         | true ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_OEIOnGround_67
                         | _ -> self.r_127 <- false  end)
              | Oeitakeoff_OEIOnGround_67 ->
                  (if self.r_127 then ()) ;
                  (begin match (>=) l_124 
                                    ((-.) (( *. ) 1.1  vstallflaps) 
                                          (( *. ) (( *. ) 0.5  a)  dt)) with
                         | true ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_ClimbOEI_68
                         | _ -> self.r_127 <- false  end)
              | Oeitakeoff_ClimbOEI_68 ->
                  (if self.r_127 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_127 <- true ;
                             self.s_126 <- Oeitakeoff_ClimbOEI_68
                         | _ -> self.r_127 <- false  end)
               end) ;
       (let (l_123:float) = self.h_115 in
        (begin match self.s_126 with
               | Oeitakeoff_TakeoffBeforeDecisionSpeed_63 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- false ;
                   self.oei_118 <- false ;
                   self.ww_121 <- true ;
                   self.lg_116 <- true ;
                   self.fl_114 <- true ;
                   self.thr_119 <- true ;
                   self.h_115 <- l_123 ;
                   self.x_122 <- (+.) ((+.) l_125  (( *. ) l_124  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  a)  dt) 
                                              dt) ;
                   self.vel_120 <- (+.) l_124  (( *. ) a  dt)
               | Oeitakeoff_Stop_64 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- false ;
                   self.oei_118 <- true ;
                   self.ww_121 <- true ;
                   self.lg_116 <- true ;
                   self.fl_114 <- true ;
                   self.thr_119 <- false ;
                   self.h_115 <- l_123 ;
                   self.x_122 <- (-.) ((+.) l_125  (( *. ) l_124  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  b)  dt) 
                                              dt) ;
                   self.vel_120 <- (-.) l_124  (( *. ) b  dt)
               | Oeitakeoff_StopFully_65 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- false ;
                   self.oei_118 <- true ;
                   self.ww_121 <- true ;
                   self.lg_116 <- true ;
                   self.fl_114 <- true ;
                   self.thr_119 <- false ;
                   self.h_115 <- l_123 ;
                   self.x_122 <- l_125 ; self.vel_120 <- 0.
               | Oeitakeoff_TakeoffAfterDecisionSpeed_66 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- false ;
                   self.oei_118 <- false ;
                   self.ww_121 <- true ;
                   self.lg_116 <- true ;
                   self.fl_114 <- true ;
                   self.thr_119 <- true ;
                   self.h_115 <- l_123 ;
                   self.x_122 <- (+.) ((+.) l_125  (( *. ) l_124  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  a)  dt) 
                                              dt) ;
                   self.vel_120 <- (+.) l_124  (( *. ) a  dt)
               | Oeitakeoff_OEIOnGround_67 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- false ;
                   self.oei_118 <- true ;
                   self.ww_121 <- true ;
                   self.lg_116 <- true ;
                   self.fl_114 <- true ;
                   self.thr_119 <- true ;
                   self.h_115 <- l_123 ;
                   self.x_122 <- (+.) ((+.) l_125  (( *. ) l_124  dt)) 
                                      (( *. ) (( *. ) (( *. ) (( *. ) 
                                                                 0.5  0.5)  
                                                              a)  dt)  
                                              dt) ;
                   self.vel_120 <- (+.) l_124  (( *. ) (( *. ) 0.5  a)  dt)
               | Oeitakeoff_ClimbOEI_68 ->
                   (if self.r_127 then ()) ;
                   self.obsclear_117 <- true ;
                   self.oei_118 <- true ;
                   self.ww_121 <- false ;
                   self.lg_116 <- false ;
                   self.fl_114 <- true ;
                   self.thr_119 <- true ;
                   self.h_115 <- (+.) l_123  (( *. ) coei  dt) ;
                   self.x_122 <- (+.) ((+.) l_125  (( *. ) l_124  dt)) 
                                      (( *. ) (( *. ) (( *. ) (( *. ) 
                                                                 0.5  0.5)  
                                                              a)  dt)  
                                              dt) ;
                   self.vel_120 <- (+.) l_124  (( *. ) (( *. ) 0.5  a)  dt)
                end) ;
        (self.x_122 ,
         self.vel_120 ,
         self.h_115 ,
         self.thr_119 ,
         self.fl_114 ,
         self.lg_116 , self.ww_121 , self.oei_118 , self.obsclear_117)))):
    float * float * float * bool * bool * bool * bool * bool * bool) in
  Node { alloc = takeoff_alloc; reset = takeoff_reset ; step = takeoff_step }
type ('q ,
      'p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_130 : 'q ;
    mutable h_137 : 'p ;
    mutable i_135 : 'o ;
    mutable h_133 : 'n ;
    mutable result_132 : 'm ;
    mutable i_161 : 'l ;
    mutable r_160 : 'k ;
    mutable s_159 : 'j ;
    mutable x_155 : 'i ;
    mutable ww_154 : 'h ;
    mutable vel_153 : 'g ;
    mutable thr_152 : 'f ;
    mutable oei_151 : 'e ;
    mutable obsclear_150 : 'd ;
    mutable lg_149 : 'c ; mutable h_148 : 'b ; mutable fl_147 : 'a }

let main (cstate_162:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_130 = false ;
      h_137 = 42. ;
      i_135 = (false:bool) ;
      h_133 = (42.:float) ;
      result_132 = (():unit) ;
      i_161 = (false:bool) ;
      r_160 = (false:bool) ;
      s_159 = (Oeitakeoff_ClimbOEI_94:state__3345) ;
      x_155 = (42.:float) ;
      ww_154 = (false:bool) ;
      vel_153 = (42.:float) ;
      thr_152 = (false:bool) ;
      oei_151 = (false:bool) ;
      obsclear_150 = (false:bool) ;
      lg_149 = (false:bool) ; h_148 = (42.:float) ; fl_147 = (false:bool) } in
  let main_step self ((time_129:float) , ()) =
    ((self.major_130 <- cstate_162.major ;
      (let (result_167:unit) =
           let h_136 = ref (infinity:float) in
           (if self.i_135 then self.h_133 <- (+.) time_129  0.) ;
           (let (z_134:bool) =
                (&&) self.major_130  ((>=) time_129  self.h_133) in
            self.h_133 <- (if z_134 then (+.) self.h_133  dt else self.h_133)
            ;
            h_136 := min !h_136  self.h_133 ;
            self.h_137 <- !h_136 ;
            self.i_135 <- false ;
            (let (trigger_131:zero) = z_134 in
             (begin match trigger_131 with
                    | true ->
                        (if self.i_161 then self.vel_153 <- vinit) ;
                        (if self.i_161 then self.h_148 <- hinit) ;
                        (if self.i_161 then self.x_155 <- xinit) ;
                        self.i_161 <- false ;
                        (let () = () in
                         let (l_157:float) = self.vel_153 in
                         let (l_158:float) = self.x_155 in
                         (begin match self.s_159 with
                                | Oeitakeoff_TakeoffBeforeDecisionSpeed_89 ->
                                    (if self.r_160 then ()) ;
                                    (begin match (((>=) l_158 
                                                        ((-.) xoei 
                                                              ((+.) (
                                                                    ( *. ) 
                                                                    l_157  dt)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt)))) ,
                                                  ((>) l_157 
                                                       ((-.) vdecision 
                                                             (( *. ) a  dt)))) with
                                           | (_ , true) ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_TakeoffAfterDecisionSpeed_92
                                           | (true , _) ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_Stop_90
                                           | _ -> self.r_160 <- false  end)
                                | Oeitakeoff_Stop_90 ->
                                    (if self.r_160 then ()) ;
                                    (begin match (<=) l_157 
                                                      ((+.) 0. 
                                                            (( *. ) b  dt)) with
                                           | true ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_StopFully_91
                                           | _ -> self.r_160 <- false  end)
                                | Oeitakeoff_StopFully_91 ->
                                    (if self.r_160 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_StopFully_91
                                           | _ -> self.r_160 <- false  end)
                                | Oeitakeoff_TakeoffAfterDecisionSpeed_92 ->
                                    (if self.r_160 then ()) ;
                                    (begin match (>=) l_158 
                                                      ((-.) xoei 
                                                            ((+.) (( *. ) 
                                                                    l_157  dt)
                                                                  
                                                                  (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt))) with
                                           | true ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_OEIOnGround_93
                                           | _ -> self.r_160 <- false  end)
                                | Oeitakeoff_OEIOnGround_93 ->
                                    (if self.r_160 then ()) ;
                                    (begin match (>=) l_157 
                                                      ((-.) (( *. ) 1.1 
                                                                    vstallflaps)
                                                            
                                                            (( *. ) (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)) with
                                           | true ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_ClimbOEI_94
                                           | _ -> self.r_160 <- false  end)
                                | Oeitakeoff_ClimbOEI_94 ->
                                    (if self.r_160 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_160 <- true ;
                                               self.s_159 <- Oeitakeoff_ClimbOEI_94
                                           | _ -> self.r_160 <- false  end)
                                 end) ;
                         (let (l_156:float) = self.h_148 in
                          (begin match self.s_159 with
                                 | Oeitakeoff_TakeoffBeforeDecisionSpeed_89 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- false ;
                                     self.oei_151 <- false ;
                                     self.ww_154 <- true ;
                                     self.lg_149 <- true ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- true ;
                                     self.h_148 <- l_156 ;
                                     self.x_155 <- (+.) ((+.) l_158 
                                                              (( *. ) 
                                                                 l_157  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  a) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_153 <- (+.) l_157 
                                                          (( *. ) a  dt)
                                 | Oeitakeoff_Stop_90 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- false ;
                                     self.oei_151 <- true ;
                                     self.ww_154 <- true ;
                                     self.lg_149 <- true ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- false ;
                                     self.h_148 <- l_156 ;
                                     self.x_155 <- (-.) ((+.) l_158 
                                                              (( *. ) 
                                                                 l_157  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  b) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_153 <- (-.) l_157 
                                                          (( *. ) b  dt)
                                 | Oeitakeoff_StopFully_91 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- false ;
                                     self.oei_151 <- true ;
                                     self.ww_154 <- true ;
                                     self.lg_149 <- true ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- false ;
                                     self.h_148 <- l_156 ;
                                     self.x_155 <- l_158 ; self.vel_153 <- 0.
                                 | Oeitakeoff_TakeoffAfterDecisionSpeed_92 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- false ;
                                     self.oei_151 <- false ;
                                     self.ww_154 <- true ;
                                     self.lg_149 <- true ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- true ;
                                     self.h_148 <- l_156 ;
                                     self.x_155 <- (+.) ((+.) l_158 
                                                              (( *. ) 
                                                                 l_157  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  a) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_153 <- (+.) l_157 
                                                          (( *. ) a  dt)
                                 | Oeitakeoff_OEIOnGround_93 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- false ;
                                     self.oei_151 <- true ;
                                     self.ww_154 <- true ;
                                     self.lg_149 <- true ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- true ;
                                     self.h_148 <- l_156 ;
                                     self.x_155 <- (+.) ((+.) l_158 
                                                              (( *. ) 
                                                                 l_157  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  0.5)
                                                                     
                                                                    a)  
                                                                   dt)  
                                                                dt) ;
                                     self.vel_153 <- (+.) l_157 
                                                          (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)
                                 | Oeitakeoff_ClimbOEI_94 ->
                                     (if self.r_160 then ()) ;
                                     self.obsclear_150 <- true ;
                                     self.oei_151 <- true ;
                                     self.ww_154 <- false ;
                                     self.lg_149 <- false ;
                                     self.fl_147 <- true ;
                                     self.thr_152 <- true ;
                                     self.h_148 <- (+.) l_156 
                                                        (( *. ) coei  dt) ;
                                     self.x_155 <- (+.) ((+.) l_158 
                                                              (( *. ) 
                                                                 l_157  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  0.5)
                                                                     
                                                                    a)  
                                                                   dt)  
                                                                dt) ;
                                     self.vel_153 <- (+.) l_157 
                                                          (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)
                                  end) ;
                          (let (obsclearp_141:bool) = self.obsclear_150 in
                           let (oeip_142:bool) = self.oei_151 in
                           let (wwp_145:bool) = self.ww_154 in
                           let (lgp_140:bool) = self.lg_149 in
                           let (flp_138:bool) = self.fl_147 in
                           let (thrp_143:bool) = self.thr_152 in
                           let (hp_139:float) = self.h_148 in
                           let (vp_144:float) = self.vel_153 in
                           let (xp_146:float) = self.x_155 in
                           let _ = print_float xp_146 in
                           let _ = print_string " " in
                           let _ = print_float vp_144 in
                           let _ = print_string " " in
                           let _ = print_float hp_139 in
                           let _ = print_string " " in
                           let _ =
                               print_string (if thrp_143
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if flp_138
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if lgp_140
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if wwp_145
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if oeip_142
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if obsclearp_141
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ = print_float (Timestamp.gettimeofday ()) in
                           self.result_132 <- print_newline ())))
                    | _ -> self.result_132 <- ()  end) ; self.result_132)) in
       cstate_162.horizon <- min cstate_162.horizon  self.h_137 ; result_167)):
    unit) in 
  let main_reset self  =
    ((self.i_135 <- true ;
      self.i_161 <- true ;
      self.r_160 <- false ;
      self.s_159 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_89 ;
      self.obsclear_150 <- false ;
      self.oei_151 <- false ;
      self.ww_154 <- true ;
      self.lg_149 <- true ; self.fl_147 <- true ; self.thr_152 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
