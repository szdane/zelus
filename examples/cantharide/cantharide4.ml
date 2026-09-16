(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type state__852 = Cantharide4_Finished_48 | Cantharide4_Running_47 
let barcelona = 0.

let girona = 100.

let fly_velocity = 80.

let car_velocity = 50.

type _print_status = unit

let print_status  = 
   let print_status_alloc _ = () in
  let print_status_reset self  =
    ((()):unit) in 
  let print_status_step self ((eventname_79:string) ,
                              (car1_77:float) ,
                              (car2_78:float) ,
                              (fly_80:float) , (zigzags_81:int)) =
    ((let _ = flush stdout in
      print_endline ((^) eventname_79 
                         ((^) ": car1=" 
                              ((^) (string_of_float car1_77) 
                                   ((^) "; car2=" 
                                        ((^) (string_of_float car2_78) 
                                             ((^) "; fly=" 
                                                  ((^) (string_of_float 
                                                          fly_80) 
                                                       ((^) "; zigzags=" 
                                                            (string_of_float 
                                                               ((/.) 
                                                                  (float 
                                                                    zigzags_81)
                                                                   2.))))))))))):
    unit) in
  Node { alloc = print_status_alloc; reset = print_status_reset ;
                                     step = print_status_step }
type ('n , 'm , 'l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _model =
  { mutable i_119 : 'n ;
    mutable major_83 : 'm ;
    mutable h_101 : 'l ;
    mutable h_99 : 'k ;
    mutable i_97 : 'j ;
    mutable next_96 : 'i ;
    mutable next_95 : 'h ;
    mutable next_94 : 'g ;
    mutable next_93 : 'f ;
    mutable zeros_88 : 'e ;
    mutable fly_87 : 'd ;
    mutable dir_86 : 'c ; mutable car2_85 : 'b ; mutable car1_84 : 'a }

let model (cstate_122:Ztypes.cstate) = 
  let Node { alloc = i_119_alloc; step = i_119_step ; reset = i_119_reset } = print_status 
   in
  let model_alloc _ =
    cstate_122.cmax <- (+) cstate_122.cmax  3 ;
    cstate_122.zmax <- (+) cstate_122.zmax  4;
    { major_83 = false ;
      h_101 = 42. ;
      h_99 = (42.:float) ;
      i_97 = (false:bool) ;
      next_96 = { zin = false; zout = 1. } ;
      next_95 = { zin = false; zout = 1. } ;
      next_94 = { zin = false; zout = 1. } ;
      next_93 = { zin = false; zout = 1. } ;
      zeros_88 = (42:int) ;
      fly_87 = { pos = 42.; der = 0. } ;
      dir_86 = (42.:float) ;
      car2_85 = { pos = 42.; der = 0. } ; car1_84 = { pos = 42.; der = 0. };
      i_119 = i_119_alloc () (* discrete *)  } in
  let model_step self ((time_82:float) , ()) =
    ((let (cindex_123:int) = cstate_122.cindex in
      let cpos_125 = ref (cindex_123:int) in
      let (zindex_124:int) = cstate_122.zindex in
      let zpos_126 = ref (zindex_124:int) in
      cstate_122.cindex <- (+) cstate_122.cindex  3 ;
      cstate_122.zindex <- (+) cstate_122.zindex  4 ;
      self.major_83 <- cstate_122.major ;
      (if cstate_122.major then
       for i_1 = cindex_123 to 2 do Zls.set cstate_122.dvec  i_1  0. done
       else ((self.fly_87.pos <- Zls.get cstate_122.cvec  !cpos_125 ;
              cpos_125 := (+) !cpos_125  1) ;
             (self.car2_85.pos <- Zls.get cstate_122.cvec  !cpos_125 ;
              cpos_125 := (+) !cpos_125  1) ;
             (self.car1_84.pos <- Zls.get cstate_122.cvec  !cpos_125 ;
              cpos_125 := (+) !cpos_125  1))) ;
      (let (result_127:(float  * float  * float  * int)) =
           let h_100 = ref (infinity:float) in
           let encore_98 = ref (false:bool) in
           let zigzagp_92 = ref (false:bool) in
           let zigzagv_91 = ref (():unit) in
           (if self.i_97 then self.fly_87.pos <- barcelona) ;
           (if self.i_97 then self.car2_85.pos <- girona) ;
           (if self.i_97 then self.car1_84.pos <- barcelona) ;
           (let (l_89:float) = self.dir_86 in
            let (l_90:int) = self.zeros_88 in
            (begin match (self.next_93.zin ,
                          self.next_94.zin ,
                          self.next_95.zin , self.next_96.zin) with
                   | (_ , _ , _ , true) | (_ , _ , true , _) | (_ ,
                                                                true , _ , _) | 
                                                               (true ,
                                                                _ , _ , _) ->
                       encore_98 := true ;
                       self.zeros_88 <- (+) l_90  1 ;
                       (let () =
                            i_119_step self.i_119
                              ("zigzag" ,
                               self.car1_84.pos ,
                               self.car2_85.pos ,
                               self.fly_87.pos , self.zeros_88) in
                        zigzagp_92 := true ;
                        zigzagv_91 := () ; self.dir_86 <- (~-.) l_89)
                   | _ -> ()  end) ;
            self.h_99 <- (if !encore_98 then 0. else infinity) ;
            h_100 := min !h_100  self.h_99 ;
            self.h_101 <- !h_100 ;
            self.i_97 <- false ;
            self.next_96.zout <- (-.) self.car1_84.pos  self.fly_87.pos ;
            self.next_95.zout <- (-.) self.car2_85.pos  self.fly_87.pos ;
            self.next_94.zout <- (-.) self.fly_87.pos  self.car1_84.pos ;
            self.next_93.zout <- (-.) self.fly_87.pos  self.car2_85.pos ;
            self.fly_87.der <- ( *. ) self.dir_86  fly_velocity ;
            self.car2_85.der <- (~-.) car_velocity ;
            self.car1_84.der <- car_velocity ;
            (self.car1_84.pos ,
             self.car2_85.pos , self.fly_87.pos , self.zeros_88)) in
       cstate_122.horizon <- min cstate_122.horizon  self.h_101 ;
       cpos_125 := cindex_123 ;
       (if cstate_122.major then
        (((Zls.set cstate_122.cvec  !cpos_125  self.fly_87.pos ;
           cpos_125 := (+) !cpos_125  1) ;
          (Zls.set cstate_122.cvec  !cpos_125  self.car2_85.pos ;
           cpos_125 := (+) !cpos_125  1) ;
          (Zls.set cstate_122.cvec  !cpos_125  self.car1_84.pos ;
           cpos_125 := (+) !cpos_125  1)) ;
         ((self.next_96.zin <- false) ;
          (self.next_95.zin <- false) ;
          (self.next_94.zin <- false) ; (self.next_93.zin <- false)))
        else (((self.next_96.zin <- Zls.get_zin cstate_122.zinvec  !zpos_126
                ; zpos_126 := (+) !zpos_126  1) ;
               (self.next_95.zin <- Zls.get_zin cstate_122.zinvec  !zpos_126
                ; zpos_126 := (+) !zpos_126  1) ;
               (self.next_94.zin <- Zls.get_zin cstate_122.zinvec  !zpos_126
                ; zpos_126 := (+) !zpos_126  1) ;
               (self.next_93.zin <- Zls.get_zin cstate_122.zinvec  !zpos_126
                ; zpos_126 := (+) !zpos_126  1)) ;
              zpos_126 := zindex_124 ;
              ((Zls.set cstate_122.zoutvec  !zpos_126  self.next_96.zout ;
                zpos_126 := (+) !zpos_126  1) ;
               (Zls.set cstate_122.zoutvec  !zpos_126  self.next_95.zout ;
                zpos_126 := (+) !zpos_126  1) ;
               (Zls.set cstate_122.zoutvec  !zpos_126  self.next_94.zout ;
                zpos_126 := (+) !zpos_126  1) ;
               (Zls.set cstate_122.zoutvec  !zpos_126  self.next_93.zout ;
                zpos_126 := (+) !zpos_126  1)) ;
              ((Zls.set cstate_122.dvec  !cpos_125  self.fly_87.der ;
                cpos_125 := (+) !cpos_125  1) ;
               (Zls.set cstate_122.dvec  !cpos_125  self.car2_85.der ;
                cpos_125 := (+) !cpos_125  1) ;
               (Zls.set cstate_122.dvec  !cpos_125  self.car1_84.der ;
                cpos_125 := (+) !cpos_125  1)))) ; result_127)):float *
                                                                float *
                                                                float * int) in
  
  let model_reset self  =
    ((self.zeros_88 <- 0 ;
      self.dir_86 <- 1. ; self.i_97 <- true ; i_119_reset self.i_119 ):
    unit) in
  Node { alloc = model_alloc; step = model_step ; reset = model_reset }
type ('l , 'k , 'j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_121 : 'l ;
    mutable i_120 : 'k ;
    mutable major_103 : 'j ;
    mutable next_114 : 'i ;
    mutable h_109 : 'h ;
    mutable h_107 : 'g ;
    mutable r_105 : 'f ;
    mutable s_104 : 'e ;
    mutable zigzags_113 : 'd ;
    mutable fly_112 : 'c ; mutable car2_111 : 'b ; mutable car1_110 : 'a }

let main (cstate_128:Ztypes.cstate) = 
  let Node { alloc = i_121_alloc; step = i_121_step ; reset = i_121_reset } = model 
  cstate_128 in 
  let Node { alloc = i_120_alloc; step = i_120_step ; reset = i_120_reset } = print_status 
   in
  let main_alloc _ =
    cstate_128.zmax <- (+) cstate_128.zmax  1;
    { major_103 = false ;
      next_114 = { zin = false; zout = 1. } ;
      h_109 = 42. ;
      h_107 = (42.:float) ;
      r_105 = (false:bool) ;
      s_104 = (Cantharide4_Finished_48:state__852) ;
      zigzags_113 = (42:int) ;
      fly_112 = (42.:float) ; car2_111 = (42.:float) ; car1_110 = (42.:float);
      i_121 = i_121_alloc () (* continuous *)  ;
      i_120 = i_120_alloc () (* discrete *)  } in
  let main_step self ((time_102:float) , ()) =
    ((let (zindex_130:int) = cstate_128.zindex in
      let zpos_132 = ref (zindex_130:int) in
      cstate_128.zindex <- (+) cstate_128.zindex  1 ;
      self.major_103 <- cstate_128.major ;
      (let (result_133:unit) =
           let h_108 = ref (infinity:float) in
           let encore_106 = ref (false:bool) in
           (begin match self.s_104 with
                  | Cantharide4_Running_47 ->
                      (if self.r_105 then
                       (i_121_reset self.i_121  ; i_120_reset self.i_120 )) ;
                      (let ((copy_115:float) ,
                            (copy_116:float) ,
                            (copy_117:float) , (copy_118:int)) =
                           i_121_step self.i_121 (time_102 , ()) in
                       self.car1_110 <- copy_115 ;
                       self.next_114.zout <- (-.) self.car1_110  girona ;
                       self.zigzags_113 <- copy_118 ;
                       self.fly_112 <- copy_117 ;
                       self.car2_111 <- copy_116 ;
                       (begin match self.next_114.zin with
                              | true ->
                                  encore_106 := true ;
                                  (let _ =
                                       i_120_step self.i_120
                                         ("done" ,
                                          self.car1_110 ,
                                          self.car2_111 ,
                                          self.fly_112 , self.zigzags_113) in
                                   self.r_105 <- true ;
                                   self.s_104 <- Cantharide4_Finished_48)
                              | _ -> self.r_105 <- false  end))
                  | Cantharide4_Finished_48 ->
                      (if self.r_105 then ()) ; self.r_105 <- false
                   end) ;
           self.h_107 <- (if !encore_106 then 0. else infinity) ;
           h_108 := min !h_108  self.h_107 ; self.h_109 <- !h_108 ; () in
       cstate_128.horizon <- min cstate_128.horizon  self.h_109 ;
       (if cstate_128.major then (((self.next_114.zin <- false)))
        else (((self.next_114.zin <- Zls.get_zin cstate_128.zinvec  !zpos_132
                ; zpos_132 := (+) !zpos_132  1)) ;
              zpos_132 := zindex_130 ;
              ((Zls.set cstate_128.zoutvec  !zpos_132  self.next_114.zout ;
                zpos_132 := (+) !zpos_132  1)))) ; result_133)):unit) in 
  let main_reset self  =
    ((self.r_105 <- false ;
      self.s_104 <- Cantharide4_Running_47 ;
      i_121_reset self.i_121  ; i_120_reset self.i_120 ):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
