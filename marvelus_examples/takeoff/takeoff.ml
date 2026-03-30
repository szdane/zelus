(* The Zelus compiler, version 2.2-dev
  (2026-03-30-2:36) *)
open Ztypes
type state__1494 = Takeoff_Cruise_68 | Takeoff_Climb_67 | Takeoff_Takeoff_66 
type state__1493 = Takeoff_Cruise_49 | Takeoff_Climb_48 | Takeoff_Takeoff_47 
let vstallflaps = 20.

let vstallclean = 25.

let xinit = 0.

let vinit = 10.

let hinit = 0.

let a = 2.

let dt = 0.1

let c = 4.

let hceiling = 6.5

let lrunway = 96.

type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_100 : 'j ;
    mutable r_99 : 'i ;
    mutable s_98 : 'h ;
    mutable x_94 : 'g ;
    mutable ww_93 : 'f ;
    mutable vel_92 : 'e ;
    mutable thr_91 : 'd ;
    mutable lg_90 : 'c ; mutable h_89 : 'b ; mutable fl_88 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_100 = (false:bool) ;
      r_99 = (false:bool) ;
      s_98 = (Takeoff_Cruise_49:state__1493) ;
      x_94 = (42.:float) ;
      ww_93 = (false:bool) ;
      vel_92 = (42.:float) ;
      thr_91 = (false:bool) ;
      lg_90 = (false:bool) ; h_89 = (42.:float) ; fl_88 = (false:bool) } in
  let exec_reset self  =
    ((self.i_100 <- true ;
      self.r_99 <- false ;
      self.s_98 <- Takeoff_Takeoff_47 ;
      self.ww_93 <- true ;
      self.lg_90 <- true ; self.fl_88 <- true ; self.thr_91 <- true):
    unit) in 
  let exec_step self () =
    (((if self.i_100 then self.h_89 <- hinit) ;
      (if self.i_100 then self.x_94 <- xinit) ;
      (if self.i_100 then self.vel_92 <- vinit) ;
      self.i_100 <- false ;
      (let (l_95:float) = self.h_89 in
       let (l_96:float) = self.vel_92 in
       (begin match self.s_98 with
              | Takeoff_Takeoff_47 ->
                  (if self.r_99 then ()) ;
                  (begin match (>) l_96 
                                   ((-.) (( *. ) 1.1  vstallflaps) 
                                         (( *. ) a  dt)) with
                         | true ->
                             self.r_99 <- true ;
                             self.s_98 <- Takeoff_Climb_48
                         | _ -> self.r_99 <- false  end)
              | Takeoff_Climb_48 ->
                  (if self.r_99 then ()) ;
                  (begin match (>=) l_95  ((-.) hceiling  (( *. ) c  dt)) with
                         | true ->
                             self.r_99 <- true ;
                             self.s_98 <- Takeoff_Cruise_49
                         | _ -> self.r_99 <- false  end)
              | Takeoff_Cruise_49 ->
                  (if self.r_99 then ()) ;
                  (begin match false with
                         | true ->
                             self.r_99 <- true ;
                             self.s_98 <- Takeoff_Cruise_49
                         | _ -> self.r_99 <- false  end)
               end) ;
       (let (l_97:float) = self.x_94 in
        (begin match self.s_98 with
               | Takeoff_Takeoff_47 ->
                   (if self.r_99 then ()) ;
                   self.ww_93 <- true ;
                   self.lg_90 <- true ;
                   self.fl_88 <- true ;
                   self.thr_91 <- true ;
                   self.vel_92 <- (+.) l_96  (( *. ) a  dt) ;
                   self.x_94 <- (+.) l_97 
                                     (( *. ) (( *. ) ((+.) l_96  self.vel_92)
                                                      0.5)  dt) ;
                   self.h_89 <- l_95
               | Takeoff_Climb_48 ->
                   (if self.r_99 then ()) ;
                   self.ww_93 <- false ;
                   self.lg_90 <- false ;
                   self.fl_88 <- true ;
                   self.thr_91 <- true ;
                   self.vel_92 <- (+.) l_96  (( *. ) a  dt) ;
                   self.x_94 <- (+.) l_97 
                                     (( *. ) (( *. ) ((+.) l_96  self.vel_92)
                                                      0.5)  dt) ;
                   self.h_89 <- (+.) l_95  (( *. ) c  dt)
               | Takeoff_Cruise_49 ->
                   (if self.r_99 then ()) ;
                   self.ww_93 <- false ;
                   self.lg_90 <- false ;
                   self.fl_88 <- false ;
                   self.thr_91 <- false ;
                   self.vel_92 <- l_96 ;
                   self.x_94 <- (+.) l_97 
                                     (( *. ) (( *. ) ((+.) l_96  self.vel_92)
                                                      0.5)  dt) ;
                   self.h_89 <- l_95
                end) ;
        (self.x_94 ,
         self.vel_92 ,
         self.h_89 , self.thr_91 , self.fl_88 , self.lg_90 , self.ww_93)))):
    float * float * float * bool * bool * bool * bool) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('o ,
      'n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_102 : 'o ;
    mutable h_109 : 'n ;
    mutable i_107 : 'm ;
    mutable h_105 : 'l ;
    mutable result_104 : 'k ;
    mutable i_129 : 'j ;
    mutable r_128 : 'i ;
    mutable s_127 : 'h ;
    mutable x_123 : 'g ;
    mutable ww_122 : 'f ;
    mutable vel_121 : 'e ;
    mutable thr_120 : 'd ;
    mutable lg_119 : 'c ; mutable h_118 : 'b ; mutable fl_117 : 'a }

let main (cstate_130:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_102 = false ;
      h_109 = 42. ;
      i_107 = (false:bool) ;
      h_105 = (42.:float) ;
      result_104 = (():unit) ;
      i_129 = (false:bool) ;
      r_128 = (false:bool) ;
      s_127 = (Takeoff_Cruise_68:state__1494) ;
      x_123 = (42.:float) ;
      ww_122 = (false:bool) ;
      vel_121 = (42.:float) ;
      thr_120 = (false:bool) ;
      lg_119 = (false:bool) ; h_118 = (42.:float) ; fl_117 = (false:bool) } in
  let main_step self ((time_101:float) , ()) =
    ((self.major_102 <- cstate_130.major ;
      (let (result_135:unit) =
           let h_108 = ref (infinity:float) in
           (if self.i_107 then self.h_105 <- (+.) time_101  0.) ;
           (let (z_106:bool) =
                (&&) self.major_102  ((>=) time_101  self.h_105) in
            self.h_105 <- (if z_106 then (+.) self.h_105  dt else self.h_105)
            ;
            h_108 := min !h_108  self.h_105 ;
            self.h_109 <- !h_108 ;
            self.i_107 <- false ;
            (let (trigger_103:zero) = z_106 in
             (begin match trigger_103 with
                    | true ->
                        (if self.i_129 then self.h_118 <- hinit) ;
                        (if self.i_129 then self.x_123 <- xinit) ;
                        (if self.i_129 then self.vel_121 <- vinit) ;
                        self.i_129 <- false ;
                        (let () = () in
                         let (l_124:float) = self.h_118 in
                         let (l_125:float) = self.vel_121 in
                         (begin match self.s_127 with
                                | Takeoff_Takeoff_66 ->
                                    (if self.r_128 then ()) ;
                                    (begin match (>) l_125 
                                                     ((-.) (( *. ) 1.1 
                                                                   vstallflaps)
                                                            (( *. ) a  dt)) with
                                           | true ->
                                               self.r_128 <- true ;
                                               self.s_127 <- Takeoff_Climb_67
                                           | _ -> self.r_128 <- false  end)
                                | Takeoff_Climb_67 ->
                                    (if self.r_128 then ()) ;
                                    (begin match (>=) l_124 
                                                      ((-.) hceiling 
                                                            (( *. ) c  dt)) with
                                           | true ->
                                               self.r_128 <- true ;
                                               self.s_127 <- Takeoff_Cruise_68
                                           | _ -> self.r_128 <- false  end)
                                | Takeoff_Cruise_68 ->
                                    (if self.r_128 then ()) ;
                                    (begin match false with
                                           | true ->
                                               self.r_128 <- true ;
                                               self.s_127 <- Takeoff_Cruise_68
                                           | _ -> self.r_128 <- false  end)
                                 end) ;
                         (let (l_126:float) = self.x_123 in
                          (begin match self.s_127 with
                                 | Takeoff_Takeoff_66 ->
                                     (if self.r_128 then ()) ;
                                     self.ww_122 <- true ;
                                     self.lg_119 <- true ;
                                     self.fl_117 <- true ;
                                     self.thr_120 <- true ;
                                     self.vel_121 <- (+.) l_125 
                                                          (( *. ) a  dt) ;
                                     self.x_123 <- (+.) l_126 
                                                        (( *. ) (( *. ) 
                                                                   ((+.) 
                                                                    l_125 
                                                                    self.vel_121)
                                                                    0.5)  
                                                                dt) ;
                                     self.h_118 <- l_124
                                 | Takeoff_Climb_67 ->
                                     (if self.r_128 then ()) ;
                                     self.ww_122 <- false ;
                                     self.lg_119 <- false ;
                                     self.fl_117 <- true ;
                                     self.thr_120 <- true ;
                                     self.vel_121 <- (+.) l_125 
                                                          (( *. ) a  dt) ;
                                     self.x_123 <- (+.) l_126 
                                                        (( *. ) (( *. ) 
                                                                   ((+.) 
                                                                    l_125 
                                                                    self.vel_121)
                                                                    0.5)  
                                                                dt) ;
                                     self.h_118 <- (+.) l_124  (( *. ) c  dt)
                                 | Takeoff_Cruise_68 ->
                                     (if self.r_128 then ()) ;
                                     self.ww_122 <- false ;
                                     self.lg_119 <- false ;
                                     self.fl_117 <- false ;
                                     self.thr_120 <- false ;
                                     self.vel_121 <- l_125 ;
                                     self.x_123 <- (+.) l_126 
                                                        (( *. ) (( *. ) 
                                                                   ((+.) 
                                                                    l_125 
                                                                    self.vel_121)
                                                                    0.5)  
                                                                dt) ;
                                     self.h_118 <- l_124
                                  end) ;
                          (let (wwp_115:bool) = self.ww_122 in
                           let (lgp_112:bool) = self.lg_119 in
                           let (flp_110:bool) = self.fl_117 in
                           let (thrp_113:bool) = self.thr_120 in
                           let (hp_111:float) = self.h_118 in
                           let (vp_114:float) = self.vel_121 in
                           let (xp_116:float) = self.x_123 in
                           let _ = print_float xp_116 in
                           let _ = print_string " " in
                           let _ = print_float vp_114 in
                           let _ = print_string " " in
                           let _ = print_float hp_111 in
                           let _ = print_string " " in
                           let _ =
                               print_string (if thrp_113
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if flp_110
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if lgp_112
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ =
                               print_string (if wwp_115
                                             then "true"
                                             else "false") in
                           let _ = print_string " " in
                           let _ = print_string " " in
                           let _ = print_float (Timestamp.gettimeofday ()) in
                           self.result_104 <- print_newline ())))
                    | _ -> self.result_104 <- ()  end) ; self.result_104)) in
       cstate_130.horizon <- min cstate_130.horizon  self.h_109 ; result_135)):
    unit) in 
  let main_reset self  =
    ((self.i_107 <- true ;
      self.i_129 <- true ;
      self.r_128 <- false ;
      self.s_127 <- Takeoff_Takeoff_66 ;
      self.ww_122 <- true ;
      self.lg_119 <- true ; self.fl_117 <- true ; self.thr_120 <- true):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
