(* The Zelus compiler, version 2.2-dev
  (2026-03-31-0:56) *)
open Ztypes
type state__3273 =
Oeitakeoff_ClimbOEI_87
| Oeitakeoff_OEIOnGround_86
| Oeitakeoff_TakeoffAfterDecisionSpeed_85
| Oeitakeoff_StopFully_84
| Oeitakeoff_Stop_83 | Oeitakeoff_TakeoffBeforeDecisionSpeed_82 
type state__3272 =
Oeitakeoff_ClimbOEI_63
| Oeitakeoff_OEIOnGround_62
| Oeitakeoff_TakeoffAfterDecisionSpeed_61
| Oeitakeoff_StopFully_60
| Oeitakeoff_Stop_59 | Oeitakeoff_TakeoffBeforeDecisionSpeed_58 
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

type ('k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _takeoff =
  { mutable i_120 : 'k ;
    mutable r_119 : 'j ;
    mutable s_118 : 'i ;
    mutable x_114 : 'h ;
    mutable ww_113 : 'g ;
    mutable vel_112 : 'f ;
    mutable thr_111 : 'e ;
    mutable oei_110 : 'd ;
    mutable lg_109 : 'c ; mutable h_108 : 'b ; mutable fl_107 : 'a }

let takeoff  = 
  
  let takeoff_alloc _ =
    ();
    { i_120 = (false:bool) ;
      r_119 = (false:bool) ;
      s_118 = (Oeitakeoff_ClimbOEI_63:state__3272) ;
      x_114 = (42.:float) ;
      ww_113 = (false:bool) ;
      vel_112 = (42.:float) ;
      thr_111 = (false:bool) ;
      oei_110 = (false:bool) ;
      lg_109 = (false:bool) ; h_108 = (42.:float) ; fl_107 = (false:bool) } in
  let takeoff_reset self  =
    ((self.i_120 <- true ;
      self.r_119 <- false ;
      self.s_118 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_58 ;
      self.oei_110 <- false ;
      self.ww_113 <- true ;
      self.lg_109 <- true ; self.fl_107 <- true ; self.thr_111 <- true):
    unit) in 
  let takeoff_step self () =
    (((if self.i_120 then self.vel_112 <- vinit) ;
      (if self.i_120 then self.h_108 <- hinit) ;
      (if self.i_120 then self.x_114 <- xinit) ;
      self.i_120 <- false ;
      (let (l_116:float) = self.vel_112 in
       let (l_117:float) = self.x_114 in
       (begin match self.s_118 with
              | Oeitakeoff_TakeoffBeforeDecisionSpeed_58 ->
                  (if self.r_119 then ()) ;
                  (begin match (((>=) l_117 
                                      ((-.) xoei 
                                            ((+.) (( *. ) l_116  dt) 
                                                  (( *. ) (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)  
                                                          dt)))) ,
                                ((>) l_116  ((-.) vdecision  (( *. ) a  dt)))) with
                         | (_ , true) ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_TakeoffAfterDecisionSpeed_61
                         | (true , _) ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_Stop_59
                         | _ -> self.r_119 <- false  end)
              | Oeitakeoff_Stop_59 ->
                  (if self.r_119 then ()) ;
                  (begin match (<=) l_116  ((+.) 0.  (( *. ) b  dt)) with
                         | true ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_StopFully_60
                         | _ -> self.r_119 <- false  end)
              | Oeitakeoff_StopFully_60 ->
                  (if self.r_119 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_StopFully_60
                         | _ -> self.r_119 <- false  end)
              | Oeitakeoff_TakeoffAfterDecisionSpeed_61 ->
                  (if self.r_119 then ()) ;
                  (begin match (>=) l_117 
                                    ((-.) xoei 
                                          ((+.) (( *. ) l_116  dt) 
                                                (( *. ) (( *. ) (( *. ) 
                                                                   0.5  a) 
                                                                dt)  
                                                        dt))) with
                         | true ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_OEIOnGround_62
                         | _ -> self.r_119 <- false  end)
              | Oeitakeoff_OEIOnGround_62 ->
                  (if self.r_119 then ()) ;
                  (begin match (>=) l_116 
                                    ((-.) (( *. ) 1.1  vstallflaps) 
                                          (( *. ) (( *. ) 0.5  a)  dt)) with
                         | true ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_ClimbOEI_63
                         | _ -> self.r_119 <- false  end)
              | Oeitakeoff_ClimbOEI_63 ->
                  (if self.r_119 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_119 <- true ;
                             self.s_118 <- Oeitakeoff_ClimbOEI_63
                         | _ -> self.r_119 <- false  end)
               end) ;
       (let (l_115:float) = self.h_108 in
        (begin match self.s_118 with
               | Oeitakeoff_TakeoffBeforeDecisionSpeed_58 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- false ;
                   self.ww_113 <- true ;
                   self.lg_109 <- true ;
                   self.fl_107 <- true ;
                   self.thr_111 <- true ;
                   self.h_108 <- l_115 ;
                   self.x_114 <- (+.) ((+.) l_117  (( *. ) l_116  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  a)  dt) 
                                              dt) ;
                   self.vel_112 <- (+.) l_116  (( *. ) a  dt)
               | Oeitakeoff_Stop_59 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- true ;
                   self.ww_113 <- true ;
                   self.lg_109 <- true ;
                   self.fl_107 <- true ;
                   self.thr_111 <- false ;
                   self.h_108 <- l_115 ;
                   self.x_114 <- (-.) ((+.) l_117  (( *. ) l_116  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  b)  dt) 
                                              dt) ;
                   self.vel_112 <- (-.) l_116  (( *. ) b  dt)
               | Oeitakeoff_StopFully_60 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- true ;
                   self.ww_113 <- true ;
                   self.lg_109 <- true ;
                   self.fl_107 <- true ;
                   self.thr_111 <- false ;
                   self.h_108 <- l_115 ;
                   self.x_114 <- l_117 ; self.vel_112 <- 0.
               | Oeitakeoff_TakeoffAfterDecisionSpeed_61 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- false ;
                   self.ww_113 <- true ;
                   self.lg_109 <- true ;
                   self.fl_107 <- true ;
                   self.thr_111 <- true ;
                   self.h_108 <- l_115 ;
                   self.x_114 <- (+.) ((+.) l_117  (( *. ) l_116  dt)) 
                                      (( *. ) (( *. ) (( *. ) 0.5  a)  dt) 
                                              dt) ;
                   self.vel_112 <- (+.) l_116  (( *. ) a  dt)
               | Oeitakeoff_OEIOnGround_62 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- true ;
                   self.ww_113 <- true ;
                   self.lg_109 <- true ;
                   self.fl_107 <- true ;
                   self.thr_111 <- true ;
                   self.h_108 <- l_115 ;
                   self.x_114 <- (+.) ((+.) l_117  (( *. ) l_116  dt)) 
                                      (( *. ) (( *. ) (( *. ) (( *. ) 
                                                                 0.5  0.5)  
                                                              a)  dt)  
                                              dt) ;
                   self.vel_112 <- (+.) l_116  (( *. ) (( *. ) 0.5  a)  dt)
               | Oeitakeoff_ClimbOEI_63 ->
                   (if self.r_119 then ()) ;
                   self.oei_110 <- true ;
                   self.ww_113 <- false ;
                   self.lg_109 <- false ;
                   self.fl_107 <- true ;
                   self.thr_111 <- true ;
                   self.h_108 <- (+.) l_115  (( *. ) coei  dt) ;
                   self.x_114 <- (+.) ((+.) l_117  (( *. ) l_116  dt)) 
                                      (( *. ) (( *. ) (( *. ) (( *. ) 
                                                                 0.5  0.5)  
                                                              a)  dt)  
                                              dt) ;
                   self.vel_112 <- (+.) l_116  (( *. ) (( *. ) 0.5  a)  dt)
                end) ;
        (self.x_114 ,
         self.vel_112 ,
         self.h_108 ,
         self.thr_111 ,
         self.fl_107 , self.lg_109 , self.ww_113 , self.oei_110)))):float *
                                                                    float *
                                                                    float *
                                                                    bool *
                                                                    bool *
                                                                    bool *
                                                                    bool *
                                                                    bool) in
  Node { alloc = takeoff_alloc; reset = takeoff_reset ; step = takeoff_step }
type ('p ,
      'o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_122 : 'p ;
    mutable h_129 : 'o ;
    mutable i_127 : 'n ;
    mutable h_125 : 'm ;
    mutable result_124 : 'l ;
    mutable i_151 : 'k ;
    mutable r_150 : 'j ;
    mutable s_149 : 'i ;
    mutable x_145 : 'h ;
    mutable ww_144 : 'g ;
    mutable vel_143 : 'f ;
    mutable thr_142 : 'e ;
    mutable oei_141 : 'd ;
    mutable lg_140 : 'c ; mutable h_139 : 'b ; mutable fl_138 : 'a }

let main (cstate_152:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_122 = false ;
      h_129 = 42. ;
      i_127 = (false:bool) ;
      h_125 = (42.:float) ;
      result_124 = (():unit) ;
      i_151 = (false:bool) ;
      r_150 = (false:bool) ;
      s_149 = (Oeitakeoff_ClimbOEI_87:state__3273) ;
      x_145 = (42.:float) ;
      ww_144 = (false:bool) ;
      vel_143 = (42.:float) ;
      thr_142 = (false:bool) ;
      oei_141 = (false:bool) ;
      lg_140 = (false:bool) ; h_139 = (42.:float) ; fl_138 = (false:bool) } in
  let main_step self ((time_121:float) , ()) =
    ((self.major_122 <- cstate_152.major ;
      (let (result_157:unit) =
           let h_128 = ref (infinity:float) in
           (if self.i_127 then self.h_125 <- (+.) time_121  0.) ;
           (let (z_126:bool) =
                (&&) self.major_122  ((>=) time_121  self.h_125) in
            self.h_125 <- (if z_126 then (+.) self.h_125  dt else self.h_125)
            ;
            h_128 := min !h_128  self.h_125 ;
            self.h_129 <- !h_128 ;
            self.i_127 <- false ;
            (let (trigger_123:zero) = z_126 in
             (begin match trigger_123 with
                    | true ->
                        (if self.i_151 then self.vel_143 <- vinit) ;
                        (if self.i_151 then self.h_139 <- hinit) ;
                        (if self.i_151 then self.x_145 <- xinit) ;
                        self.i_151 <- false ;
                        (let () = () in
                         let (l_147:float) = self.vel_143 in
                         let (l_148:float) = self.x_145 in
                         (begin match self.s_149 with
                                | Oeitakeoff_TakeoffBeforeDecisionSpeed_82 ->
                                    (if self.r_150 then ()) ;
                                    (begin match (((>=) l_148 
                                                        ((-.) xoei 
                                                              ((+.) (
                                                                    ( *. ) 
                                                                    l_147  dt)
                                                                    
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt)))) ,
                                                  ((>) l_147 
                                                       ((-.) vdecision 
                                                             (( *. ) a  dt)))) with
                                           | (_ , true) ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_TakeoffAfterDecisionSpeed_85
                                           | (true , _) ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_Stop_83
                                           | _ -> self.r_150 <- false  end)
                                | Oeitakeoff_Stop_83 ->
                                    (if self.r_150 then ()) ;
                                    (begin match (<=) l_147 
                                                      ((+.) 0. 
                                                            (( *. ) b  dt)) with
                                           | true ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_StopFully_84
                                           | _ -> self.r_150 <- false  end)
                                | Oeitakeoff_StopFully_84 ->
                                    (if self.r_150 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_StopFully_84
                                           | _ -> self.r_150 <- false  end)
                                | Oeitakeoff_TakeoffAfterDecisionSpeed_85 ->
                                    (if self.r_150 then ()) ;
                                    (begin match (>=) l_148 
                                                      ((-.) xoei 
                                                            ((+.) (( *. ) 
                                                                    l_147  dt)
                                                                  
                                                                  (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)  
                                                                    dt))) with
                                           | true ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_OEIOnGround_86
                                           | _ -> self.r_150 <- false  end)
                                | Oeitakeoff_OEIOnGround_86 ->
                                    (if self.r_150 then ()) ;
                                    (begin match (>=) l_147 
                                                      ((-.) (( *. ) 1.1 
                                                                    vstallflaps)
                                                            
                                                            (( *. ) (
                                                                    ( *. ) 
                                                                    0.5  a) 
                                                                    dt)) with
                                           | true ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_ClimbOEI_87
                                           | _ -> self.r_150 <- false  end)
                                | Oeitakeoff_ClimbOEI_87 ->
                                    (if self.r_150 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_150 <- true ;
                                               self.s_149 <- Oeitakeoff_ClimbOEI_87
                                           | _ -> self.r_150 <- false  end)
                                 end) ;
                         (let (l_146:float) = self.h_139 in
                          (begin match self.s_149 with
                                 | Oeitakeoff_TakeoffBeforeDecisionSpeed_82 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- false ;
                                     self.ww_144 <- true ;
                                     self.lg_140 <- true ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- true ;
                                     self.h_139 <- l_146 ;
                                     self.x_145 <- (+.) ((+.) l_148 
                                                              (( *. ) 
                                                                 l_147  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  a) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_143 <- (+.) l_147 
                                                          (( *. ) a  dt)
                                 | Oeitakeoff_Stop_83 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- true ;
                                     self.ww_144 <- true ;
                                     self.lg_140 <- true ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- false ;
                                     self.h_139 <- l_146 ;
                                     self.x_145 <- (-.) ((+.) l_148 
                                                              (( *. ) 
                                                                 l_147  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  b) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_143 <- (-.) l_147 
                                                          (( *. ) b  dt)
                                 | Oeitakeoff_StopFully_84 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- true ;
                                     self.ww_144 <- true ;
                                     self.lg_140 <- true ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- false ;
                                     self.h_139 <- l_146 ;
                                     self.x_145 <- l_148 ; self.vel_143 <- 0.
                                 | Oeitakeoff_TakeoffAfterDecisionSpeed_85 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- false ;
                                     self.ww_144 <- true ;
                                     self.lg_140 <- true ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- true ;
                                     self.h_139 <- l_146 ;
                                     self.x_145 <- (+.) ((+.) l_148 
                                                              (( *. ) 
                                                                 l_147  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    0.5  a) 
                                                                   dt)  
                                                                dt) ;
                                     self.vel_143 <- (+.) l_147 
                                                          (( *. ) a  dt)
                                 | Oeitakeoff_OEIOnGround_86 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- true ;
                                     self.ww_144 <- true ;
                                     self.lg_140 <- true ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- true ;
                                     self.h_139 <- l_146 ;
                                     self.x_145 <- (+.) ((+.) l_148 
                                                              (( *. ) 
                                                                 l_147  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  0.5)
                                                                     
                                                                    a)  
                                                                   dt)  
                                                                dt) ;
                                     self.vel_143 <- (+.) l_147 
                                                          (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)
                                 | Oeitakeoff_ClimbOEI_87 ->
                                     (if self.r_150 then ()) ;
                                     self.oei_141 <- true ;
                                     self.ww_144 <- false ;
                                     self.lg_140 <- false ;
                                     self.fl_138 <- true ;
                                     self.thr_142 <- true ;
                                     self.h_139 <- (+.) l_146 
                                                        (( *. ) coei  dt) ;
                                     self.x_145 <- (+.) ((+.) l_148 
                                                              (( *. ) 
                                                                 l_147  dt)) 
                                                        (( *. ) (( *. ) 
                                                                   (( *. ) 
                                                                    (
                                                                    ( *. ) 
                                                                    0.5  0.5)
                                                                     
                                                                    a)  
                                                                   dt)  
                                                                dt) ;
                                     self.vel_143 <- (+.) l_147 
                                                          (( *. ) (( *. ) 
                                                                    0.5  a) 
                                                                  dt)
                                  end) ;
                          (let (oeip_133:bool) = self.oei_141 in
                           let (wwp_136:bool) = self.ww_144 in
                           let (lgp_132:bool) = self.lg_140 in
                           let (flp_130:bool) = self.fl_138 in
                           let (thrp_134:bool) = self.thr_142 in
                           let (hp_131:float) = self.h_139 in
                           let (vp_135:float) = self.vel_143 in
                           let (xp_137:float) = self.x_145 in
                           let _ = print_float xp_137 in
                           let _ = print_string " " in
                           let _ = print_float vp_135 in
                           let _ = print_string " " in
                           let _ = print_float hp_131 in
                           let _ = print_string " " in
                           let _ =
                               print_string (if thrp_134
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if flp_130
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if lgp_132
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if wwp_136
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if oeip_133
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ = print_string " " in
                           let _ = print_float (Timestamp.gettimeofday ()) in
                           self.result_124 <- print_newline ())))
                    | _ -> self.result_124 <- ()  end) ; self.result_124)) in
       cstate_152.horizon <- min cstate_152.horizon  self.h_129 ; result_157)):
    unit) in 
  let main_reset self  =
    ((self.i_127 <- true ;
      self.i_151 <- true ;
      self.r_150 <- false ;
      self.s_149 <- Oeitakeoff_TakeoffBeforeDecisionSpeed_82 ;
      self.oei_141 <- false ;
      self.ww_144 <- true ;
      self.lg_140 <- true ; self.fl_138 <- true ; self.thr_142 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
