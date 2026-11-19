(* The Zelus compiler, version 2.2-dev
  (2026-11-18-19:55) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

let kd = 0.5

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable i_91 : 'e ;
    mutable xk1_85 : 'd ;
    mutable errork1_82 : 'c ;
    mutable energyk1_80 : 'b ; mutable derivativek1_78 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { i_91 = (false:bool) ;
      xk1_85 = (42.:float) ;
      errork1_82 = (42.:float) ;
      energyk1_80 = (42.:float) ; derivativek1_78 = (42.:float) } in
  let exec_reset self  =
    ((self.derivativek1_78 <- 0. ; self.i_91 <- true ; self.xk1_85 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_87:float) = self.derivativek1_78 in
      let ((derivativek_77:float): float) = l_87 in
      (if self.i_91 then self.errork1_82 <- r) ;
      (let (l_89:float) = self.errork1_82 in
       let ((errork_81:float): float) = l_89 in
       let ((uk_83:float): float) =
           (-.) (( *. ) kp  errork_81)  (( *. ) kd  derivativek_77) in
       let (l_90:float) = self.xk1_85 in
       let ((xk_84:float): float) = l_90 in
       let ((copy_123:float): float) = (+.) xk_84  (( *. ) uk_83  dt) in
       self.xk1_85 <- copy_123 ;
       (let ((copy_122:float): float) = (-.) r  self.xk1_85 in
        self.errork1_82 <- copy_122 ;
        (let ((copy_121:float): float) =
             (/.) ((-.) self.errork1_82  errork_81)  dt in
         self.derivativek1_78 <- copy_121 ;
         (let ((copy_120:float): float) =
              (+.) (( *. ) self.errork1_82  self.errork1_82) 
                   (( *. ) (( *. ) 0.04  self.derivativek1_78) 
                           self.derivativek1_78) in
          (if self.i_91 then self.energyk1_80 <- ( ** ) r  2.) ;
          (let (l_88:float) = self.energyk1_80 in
           self.energyk1_80 <- copy_120 ;
           self.i_91 <- false ;
           (let ((xkbound_86:float): float) = xk_84 in
            let ((energyk_79:float): float) = l_88 in
            (xk_84 , uk_83 , errork_81 , derivativek_77)))))))):float *
                                                                float *
                                                                float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_93 : 'j ;
    mutable h_100 : 'i ;
    mutable i_98 : 'h ;
    mutable h_96 : 'g ;
    mutable result_95 : 'f ;
    mutable i_119 : 'e ;
    mutable xk1_113 : 'd ;
    mutable errork1_110 : 'c ;
    mutable energyk1_108 : 'b ; mutable derivativek1_106 : 'a }

let main (cstate_128:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_93 = false ;
      h_100 = 42. ;
      i_98 = (false:bool) ;
      h_96 = (42.:float) ;
      result_95 = (():unit) ;
      i_119 = (false:bool) ;
      xk1_113 = (42.:float) ;
      errork1_110 = (42.:float) ;
      energyk1_108 = (42.:float) ; derivativek1_106 = (42.:float) } in
  let main_step self ((time_92:float) , ()) =
    ((self.major_93 <- cstate_128.major ;
      (let (result_133:unit) =
           let h_99 = ref (infinity:float) in
           (if self.i_98 then self.h_96 <- (+.) time_92  0.) ;
           (let (z_97:bool) = (&&) self.major_93  ((>=) time_92  self.h_96) in
            self.h_96 <- (if z_97 then (+.) self.h_96  0.1 else self.h_96) ;
            h_99 := min !h_99  self.h_96 ;
            self.h_100 <- !h_99 ;
            self.i_98 <- false ;
            (let (trigger_94:zero) = z_97 in
             (begin match trigger_94 with
                    | true ->
                        (if self.i_119 then self.energyk1_108 <- ( ** ) r  2.)
                        ;
                        (if self.i_119 then self.errork1_110 <- r) ;
                        self.i_119 <- false ;
                        (let () = () in
                         let (l_115:float) = self.derivativek1_106 in
                         let ((derivativek_105:float): float) = l_115 in
                         let (l_117:float) = self.errork1_110 in
                         let ((errork_109:float): float) = l_117 in
                         let ((uk_111:float): float) =
                             (-.) (( *. ) kp  errork_109) 
                                  (( *. ) kd  derivativek_105) in
                         let (l_118:float) = self.xk1_113 in
                         let ((xk_112:float): float) = l_118 in
                         let ((copy_127:float): float) =
                             (+.) xk_112  (( *. ) uk_111  dt) in
                         self.xk1_113 <- copy_127 ;
                         (let ((copy_126:float): float) =
                              (-.) r  self.xk1_113 in
                          self.errork1_110 <- copy_126 ;
                          (let ((copy_125:float): float) =
                               (/.) ((-.) self.errork1_110  errork_109)  dt in
                           self.derivativek1_106 <- copy_125 ;
                           (let ((copy_124:float): float) =
                                (+.) (( *. ) self.errork1_110 
                                             self.errork1_110) 
                                     (( *. ) (( *. ) 0.04 
                                                     self.derivativek1_106) 
                                             self.derivativek1_106) in
                            let (l_116:float) = self.energyk1_108 in
                            self.energyk1_108 <- copy_124 ;
                            (let ((xkbound_114:float): float) = xk_112 in
                             let ((energyk_107:float): float) = l_116 in
                             let (derivativek_101:float) = derivativek_105 in
                             let (errork_102:float) = errork_109 in
                             let (uk_103:float) = uk_111 in
                             let (xk_104:float) = xk_112 in
                             let _ = print_float xk_104 in
                             let _ = print_string "," in
                             let _ = print_float uk_103 in
                             let _ = print_string "," in
                             let _ = print_float errork_102 in
                             let _ = print_string "," in
                             let _ = print_float derivativek_101 in
                             self.result_95 <- print_newline ())))))
                    | _ -> self.result_95 <- ()  end) ; self.result_95)) in
       cstate_128.horizon <- min cstate_128.horizon  self.h_100 ; result_133)):
    unit) in 
  let main_reset self  =
    ((self.i_98 <- true ;
      self.i_119 <- true ; self.derivativek1_106 <- 0. ; self.xk1_113 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
