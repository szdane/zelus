(* The Zelus compiler, version 2.2-dev
  (2026-07-10-6:3) *)
open Ztypes
type state__3100 =
Oeitakeoff_LevelOffOEI_91
| Oeitakeoff_StopFully_90
| Oeitakeoff_Stop_89
| Oeitakeoff_ClimbOEI_88
| Oeitakeoff_OEIOnGround_87
| Oeitakeoff_TakeoffAfterDecisionSpeed_86
| Oeitakeoff_TakeoffBeforeDecisionSpeed_85 
type state__3099 =
Oeitakeoff_LevelOffOEI_66
| Oeitakeoff_StopFully_65
| Oeitakeoff_Stop_64
| Oeitakeoff_ClimbOEI_63
| Oeitakeoff_OEIOnGround_62
| Oeitakeoff_TakeoffAfterDecisionSpeed_61
| Oeitakeoff_TakeoffBeforeDecisionSpeed_60 
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

let xoei = 105.

let xc = 300.

let lrunway = 140.292775

type ('k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _takeoff =
  { mutable i_124 : 'k ;
    mutable r_123 : 'j ;
    mutable s_122 : 'i ;
    mutable x_118 : 'h ;
    mutable ww_117 : 'g ;
    mutable vel_116 : 'f ;
    mutable thr_115 : 'e ;
    mutable oei_114 : 'd ;
    mutable lg_113 : 'c ; mutable h_112 : 'b ; mutable fl_111 : 'a }

let takeoff  = 
  
  let takeoff_alloc _ =
    ();
    { i_124 = (false:bool) ;
      r_123 = (false:bool) ;
      s_122 = (Oeitakeoff_LevelOffOEI_66:state__3099) ;
      x_118 = (42.:float) ;
      ww_117 = (false:bool) ;
      vel_116 = (42.:float) ;
      thr_115 = (false:bool) ;
      oei_114 = (false:bool) ;
      lg_113 = (false:bool) ; h_112 = (42.:float) ; fl_111 = (false:bool) } in
  let takeoff_reset self  =
    ((self.i_124 <- true ;
      self.r_123 <- false ;
      self.s_122 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_60 ;
      self.oei_114 <- false ;
      self.ww_117 <- true ;
      self.lg_113 <- true ; self.fl_111 <- true ; self.thr_115 <- true):
    unit) in 
  let takeoff_step self () =
    (((if self.i_124 then self.vel_116 <- vinit) ;
      (if self.i_124 then self.h_112 <- hinit) ;
      (if self.i_124 then self.x_118 <- xinit) ;
      self.i_124 <- false ;
      (let (l_119:float) = self.h_112 in
       let (l_120:float) = self.vel_116 in
       let (l_121:float) = self.x_118 in
       (begin match self.s_122 with
              | Oeitakeoff_TakeoffBeforeDecisionSpeed_60 ->
                  (if self.r_123 then ()) ;
                  (begin match (((>=) l_121 
                                      ((-.) xoei 
                                            ((+.) (( *. ) l_120  dt) 
                                                  (( *. ) (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)  
                                                          dt)))) ,
                                ((>) l_120  ((-.) vdecision  (( *. ) a  dt)))) with
                         | (_ , true) ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_TakeoffAfterDecisionSpeed_61
                         | (true , _) ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_Stop_64
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_TakeoffAfterDecisionSpeed_61 ->
                  (if self.r_123 then ()) ;
                  (begin match (>=) l_121 
                                    ((-.) xoei 
                                          ((+.) (( *. ) l_120  dt) 
                                                (( *. ) (( *. ) (( *. ) 
                                                                   0.5  a) 
                                                                dt)  
                                                        dt))) with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_OEIOnGround_62
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_OEIOnGround_62 ->
                  (if self.r_123 then ()) ;
                  (begin match (>=) l_120 
                                    ((-.) (( *. ) 1.1  vstallflaps) 
                                          (( *. ) (( *. ) 0.5  a)  dt)) with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_ClimbOEI_63
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_ClimbOEI_63 ->
                  (if self.r_123 then ()) ;
                  (begin match (>=) l_119  ((-.) hceiling  (( *. ) coei  dt)) with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_LevelOffOEI_66
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_Stop_64 ->
                  (if self.r_123 then ()) ;
                  (begin match (<=) l_120  ((+.) 0.  (( *. ) b  dt)) with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_StopFully_65
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_StopFully_65 ->
                  (if self.r_123 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_StopFully_65
                         | _ -> self.r_123 <- false  end)
              | Oeitakeoff_LevelOffOEI_66 ->
                  (if self.r_123 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_123 <- true ;
                             self.s_122 <- Oeitakeoff_LevelOffOEI_66
                         | _ -> self.r_123 <- false  end)
               end) ;
       (begin match self.s_122 with
              | Oeitakeoff_TakeoffBeforeDecisionSpeed_60 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- false ;
                  self.ww_117 <- true ;
                  self.lg_113 <- true ;
                  self.fl_111 <- true ;
                  self.thr_115 <- true ;
                  self.h_112 <- l_119 ;
                  self.vel_116 <- (+.) l_120  (( *. ) a  dt) ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
              | Oeitakeoff_TakeoffAfterDecisionSpeed_61 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- false ;
                  self.ww_117 <- true ;
                  self.lg_113 <- true ;
                  self.fl_111 <- true ;
                  self.thr_115 <- true ;
                  self.h_112 <- l_119 ;
                  self.vel_116 <- (+.) l_120  (( *. ) a  dt) ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
              | Oeitakeoff_OEIOnGround_62 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- true ;
                  self.ww_117 <- true ;
                  self.lg_113 <- true ;
                  self.fl_111 <- true ;
                  self.thr_115 <- true ;
                  self.h_112 <- l_119 ;
                  self.vel_116 <- (+.) l_120  (( *. ) (( *. ) 0.5  a)  dt) ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
              | Oeitakeoff_ClimbOEI_63 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- true ;
                  self.ww_117 <- false ;
                  self.lg_113 <- false ;
                  self.fl_111 <- true ;
                  self.thr_115 <- true ;
                  self.h_112 <- (+.) l_119  (( *. ) coei  dt) ;
                  self.vel_116 <- (+.) l_120  (( *. ) (( *. ) 0.5  a)  dt) ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
              | Oeitakeoff_Stop_64 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- true ;
                  self.ww_117 <- true ;
                  self.lg_113 <- true ;
                  self.fl_111 <- true ;
                  self.thr_115 <- false ;
                  self.h_112 <- l_119 ;
                  self.vel_116 <- (-.) l_120  (( *. ) b  dt) ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
              | Oeitakeoff_StopFully_65 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- true ;
                  self.ww_117 <- true ;
                  self.lg_113 <- true ;
                  self.fl_111 <- true ;
                  self.thr_115 <- false ;
                  self.h_112 <- l_119 ;
                  self.x_118 <- l_121 ; self.vel_116 <- 0.
              | Oeitakeoff_LevelOffOEI_66 ->
                  (if self.r_123 then ()) ;
                  self.oei_114 <- true ;
                  self.ww_117 <- false ;
                  self.lg_113 <- false ;
                  self.fl_111 <- true ;
                  self.thr_115 <- true ;
                  self.h_112 <- l_119 ;
                  self.vel_116 <- l_120 ;
                  self.x_118 <- (+.) l_121 
                                     (( *. ) (( *. ) ((+.) l_120 
                                                           self.vel_116)  
                                                     0.5)  dt)
               end) ;
       (self.x_118 ,
        self.vel_116 ,
        self.h_112 ,
        self.thr_115 , self.fl_111 , self.lg_113 , self.ww_117 , self.oei_114))):
    float * float * float * bool * bool * bool * bool * bool) in
  Node { alloc = takeoff_alloc; reset = takeoff_reset ; step = takeoff_step }
type ('p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_126 : 'p ;
    mutable h_133 : 'o ;
    mutable i_131 : 'n ;
    mutable h_129 : 'm ;
    mutable result_128 : 'l ;
    mutable i_155 : 'k ;
    mutable r_154 : 'j ;
    mutable s_153 : 'i ;
    mutable x_149 : 'h ;
    mutable ww_148 : 'g ;
    mutable vel_147 : 'f ;
    mutable thr_146 : 'e ;
    mutable oei_145 : 'd ;
    mutable lg_144 : 'c ; mutable h_143 : 'b ; mutable fl_142 : 'a }

let main (cstate_156:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_126 = false ;
      h_133 = 42. ;
      i_131 = (false:bool) ;
      h_129 = (42.:float) ;
      result_128 = (():unit) ;
      i_155 = (false:bool) ;
      r_154 = (false:bool) ;
      s_153 = (Oeitakeoff_LevelOffOEI_91:state__3100) ;
      x_149 = (42.:float) ;
      ww_148 = (false:bool) ;
      vel_147 = (42.:float) ;
      thr_146 = (false:bool) ;
      oei_145 = (false:bool) ;
      lg_144 = (false:bool) ; h_143 = (42.:float) ; fl_142 = (false:bool) } in
  let main_step self ((time_125:float) , ()) =
    ((self.major_126 <- cstate_156.major ;
      (let (result_161:unit) =
           let h_132 = ref (infinity:float) in
           (if self.i_131 then self.h_129 <- (+.) time_125  0.) ;
           (let (z_130:bool) =
                (&&) self.major_126  ((>=) time_125  self.h_129) in
            self.h_129 <- (if z_130 then (+.) self.h_129  dt else self.h_129)
            ;
            h_132 := min !h_132  self.h_129 ;
            self.h_133 <- !h_132 ;
            self.i_131 <- false ;
            (let (trigger_127:zero) = z_130 in
             (begin match trigger_127 with
                    | true ->
                        (if self.i_155 then self.vel_147 <- vinit) ;
                        (if self.i_155 then self.h_143 <- hinit) ;
                        (if self.i_155 then self.x_149 <- xinit) ;
                        self.i_155 <- false ;
                        (let () = () in
                         let (l_150:float) = self.h_143 in
                         let (l_151:float) = self.vel_147 in
                         let (l_152:float) = self.x_149 in
                         (begin match self.s_153 with
                                | Oeitakeoff_TakeoffBeforeDecisionSpeed_85 ->
                                    (if self.r_154 then ()) ;
                                    (begin match (((>=) l_152 
                                                        ((-.) xoei 
                                                              ((+.) (
                                                                    ( *. ) 
                                                                    l_151  dt)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt)))) ,
                                                  ((>) l_151 
                                                       ((-.) vdecision 
                                                             (( *. ) a  dt)))) with
                                           | (_ , true) ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_TakeoffAfterDecisionSpeed_86
                                           | (true , _) ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_Stop_89
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_TakeoffAfterDecisionSpeed_86 ->
                                    (if self.r_154 then ()) ;
                                    (begin match (>=) l_152 
                                                      ((-.) xoei 
                                                            ((+.) (( *. ) 
                                                                    l_151  dt)
                                                                  
                                                                  (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt))) with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_OEIOnGround_87
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_OEIOnGround_87 ->
                                    (if self.r_154 then ()) ;
                                    (begin match (>=) l_151 
                                                      ((-.) (( *. ) 1.1 
                                                                    vstallflaps)
                                                            
                                                            (( *. ) (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)) with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_ClimbOEI_88
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_ClimbOEI_88 ->
                                    (if self.r_154 then ()) ;
                                    (begin match (>=) l_150 
                                                      ((-.) hceiling 
                                                            (( *. ) coei  dt)) with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_LevelOffOEI_91
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_Stop_89 ->
                                    (if self.r_154 then ()) ;
                                    (begin match (<=) l_151 
                                                      ((+.) 0. 
                                                            (( *. ) b  dt)) with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_StopFully_90
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_StopFully_90 ->
                                    (if self.r_154 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_StopFully_90
                                           | _ -> self.r_154 <- false  end)
                                | Oeitakeoff_LevelOffOEI_91 ->
                                    (if self.r_154 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_154 <- true ;
                                               self.s_153 <- Oeitakeoff_LevelOffOEI_91
                                           | _ -> self.r_154 <- false  end)
                                 end) ;
                         (begin match self.s_153 with
                                | Oeitakeoff_TakeoffBeforeDecisionSpeed_85 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- false ;
                                    self.ww_148 <- true ;
                                    self.lg_144 <- true ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- true ;
                                    self.h_143 <- l_150 ;
                                    self.vel_147 <- (+.) l_151 
                                                         (( *. ) a  dt) ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                | Oeitakeoff_TakeoffAfterDecisionSpeed_86 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- false ;
                                    self.ww_148 <- true ;
                                    self.lg_144 <- true ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- true ;
                                    self.h_143 <- l_150 ;
                                    self.vel_147 <- (+.) l_151 
                                                         (( *. ) a  dt) ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                | Oeitakeoff_OEIOnGround_87 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- true ;
                                    self.ww_148 <- true ;
                                    self.lg_144 <- true ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- true ;
                                    self.h_143 <- l_150 ;
                                    self.vel_147 <- (+.) l_151 
                                                         (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                 dt) ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                | Oeitakeoff_ClimbOEI_88 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- true ;
                                    self.ww_148 <- false ;
                                    self.lg_144 <- false ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- true ;
                                    self.h_143 <- (+.) l_150 
                                                       (( *. ) coei  dt) ;
                                    self.vel_147 <- (+.) l_151 
                                                         (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                 dt) ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                | Oeitakeoff_Stop_89 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- true ;
                                    self.ww_148 <- true ;
                                    self.lg_144 <- true ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- false ;
                                    self.h_143 <- l_150 ;
                                    self.vel_147 <- (-.) l_151 
                                                         (( *. ) b  dt) ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                | Oeitakeoff_StopFully_90 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- true ;
                                    self.ww_148 <- true ;
                                    self.lg_144 <- true ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- false ;
                                    self.h_143 <- l_150 ;
                                    self.x_149 <- l_152 ; self.vel_147 <- 0.
                                | Oeitakeoff_LevelOffOEI_91 ->
                                    (if self.r_154 then ()) ;
                                    self.oei_145 <- true ;
                                    self.ww_148 <- false ;
                                    self.lg_144 <- false ;
                                    self.fl_142 <- true ;
                                    self.thr_146 <- true ;
                                    self.h_143 <- l_150 ;
                                    self.vel_147 <- l_151 ;
                                    self.x_149 <- (+.) l_152 
                                                       (( *. ) (( *. ) 
                                                                  ((+.) 
                                                                    l_151 
                                                                    self.vel_147)
                                                                   0.5)  
                                                               dt)
                                 end) ;
                         (let (oeip_137:bool) = self.oei_145 in
                          let (wwp_140:bool) = self.ww_148 in
                          let (lgp_136:bool) = self.lg_144 in
                          let (flp_134:bool) = self.fl_142 in
                          let (thrp_138:bool) = self.thr_146 in
                          let (hp_135:float) = self.h_143 in
                          let (vp_139:float) = self.vel_147 in
                          let (xp_141:float) = self.x_149 in
                          let _ = print_float xp_141 in
                          let _ = print_string " " in
                          let _ = print_float vp_139 in
                          let _ = print_string " " in
                          let _ = print_float hp_135 in
                          let _ = print_string " " in
                          let _ =
                              print_string (if thrp_138
                                            then "true"
                                            else "false") in
                          let _ = print_string " " in
                          let _ =
                              print_string (if flp_134
                                            then "true"
                                            else "false") in
                          let _ = print_string " " in
                          let _ =
                              print_string (if lgp_136
                                            then "true"
                                            else "false") in
                          let _ = print_string " " in
                          let _ =
                              print_string (if wwp_140
                                            then "true"
                                            else "false") in
                          let _ = print_string " " in
                          let _ =
                              print_string (if oeip_137
                                            then "true"
                                            else "false") in
                          let _ = print_string " " in
                          let _ = print_string " " in
                          let _ = print_float (Timestamp.gettimeofday ()) in
                          self.result_128 <- print_newline ()))
                    | _ -> self.result_128 <- ()  end) ; self.result_128)) in
       cstate_156.horizon <- min cstate_156.horizon  self.h_133 ; result_161)):
    unit) in 
  let main_reset self  =
    ((self.i_131 <- true ;
      self.i_155 <- true ;
      self.r_154 <- false ;
      self.s_153 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_85 ;
      self.oei_145 <- false ;
      self.ww_148 <- true ;
      self.lg_144 <- true ; self.fl_142 <- true ; self.thr_146 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
