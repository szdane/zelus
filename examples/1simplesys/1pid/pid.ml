(* The Zelus compiler, version 2.2-dev
  (2026-09-8-16:32) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let kd = 0.5

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable xk1_115 : 'c ;
    mutable integralk1_111 : 'b ; mutable errork_106 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_115 = (42.:float) ;
      integralk1_111 = (42.:float) ; errork_106 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_115 <- 0. ; self.errork_106 <- 1. ; self.integralk1_111 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_118:float) = self.xk1_115 in
      let ((xk_114:float): float) = l_118 in
      let ((copy_154:float): float) = (-.) r  xk_114 in
      let (l_116:float) = self.errork_106 in
      self.errork_106 <- copy_154 ;
      (let ((errorkm1_109:float): float) = l_116 in
       let ((derivativek_100:float): float) =
           (/.) ((-.) self.errork_106  errorkm1_109)  dt in
       let (l_117:float) = self.integralk1_111 in
       let ((integralk_110:float): float) = l_117 in
       let ((derivativek1help_102:float): float) =
           (+.) ((-.) (( *. ) (-2.)  self.errork_106)  integralk_110) 
                (( *. ) 0.5  derivativek_100) in
       let ((integralk1help_112:float): float) =
           (+.) ((+.) (( *. ) 0.08  self.errork_106) 
                      (( *. ) 0.99  integralk_110)) 
                (( *. ) 0.005  derivativek_100) in
       let ((errork1help_108:float): float) =
           (+.) ((-.) (( *. ) 0.8  self.errork_106) 
                      (( *. ) 0.1  integralk_110)) 
                (( *. ) 0.05  derivativek_100) in
       let ((uk_113:float): float) =
           (-.) ((+.) (( *. ) kp  self.errork_106) 
                      (( *. ) ki  integralk_110)) 
                (( *. ) kd  derivativek_100) in
       let ((copy_153:float): float) = (+.) xk_114  (( *. ) uk_113  dt) in
       self.xk1_115 <- copy_153 ;
       (let ((errork1_107:float): float) = (-.) r  self.xk1_115 in
        let ((copy_152:float): float) =
            (+.) integralk_110  (( *. ) errork1_107  dt) in
        self.integralk1_111 <- copy_152 ;
        (let ((diffenergy1_103:float): float) =
             (+.) (( *. ) (( *. ) 1.1375  errork1_107)  errork1_107) 
                  (( *. ) (( *. ) 1.25  self.integralk1_111) 
                          self.integralk1_111) in
         let ((energyk1_105:float): float) =
             (+.) (( *. ) (( *. ) 1.1375  errork1_107)  errork1_107) 
                  (( *. ) (( *. ) 1.25  self.integralk1_111) 
                          self.integralk1_111) in
         let ((energyk_104:float): float) =
             (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375  self.errork_106) 
                                      self.errork_106) 
                              (( *. ) (( *. ) 1.25  integralk_110) 
                                      integralk_110)) 
                        (( *. ) (( *. ) 0.05  derivativek_100) 
                                derivativek_100)) 
                  (( *. ) (( *. ) 1.  self.errork_106)  integralk_110) in
         let ((derivativek1_101:float): float) =
             (/.) ((-.) errork1_107  self.errork_106)  dt in
         (xk_114 , uk_113 , self.errork_106 , integralk_110 , derivativek_100))))):
    float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_120 : 'h ;
    mutable h_127 : 'g ;
    mutable i_125 : 'f ;
    mutable h_123 : 'e ;
    mutable result_122 : 'd ;
    mutable xk1_148 : 'c ;
    mutable integralk1_144 : 'b ; mutable errork_139 : 'a }

let main (cstate_158:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_120 = false ;
      h_127 = 42. ;
      i_125 = (false:bool) ;
      h_123 = (42.:float) ;
      result_122 = (():unit) ;
      xk1_148 = (42.:float) ;
      integralk1_144 = (42.:float) ; errork_139 = (42.:float) } in
  let main_step self ((time_119:float) , ()) =
    ((self.major_120 <- cstate_158.major ;
      (let (result_163:unit) =
           let h_126 = ref (infinity:float) in
           (if self.i_125 then self.h_123 <- (+.) time_119  0.) ;
           (let (z_124:bool) =
                (&&) self.major_120  ((>=) time_119  self.h_123) in
            self.h_123 <- (if z_124 then (+.) self.h_123  0.1 else self.h_123)
            ;
            h_126 := min !h_126  self.h_123 ;
            self.h_127 <- !h_126 ;
            self.i_125 <- false ;
            (let (trigger_121:zero) = z_124 in
             (begin match trigger_121 with
                    | true ->
                        let () = () in
                        let (l_151:float) = self.xk1_148 in
                        let ((xk_147:float): float) = l_151 in
                        let ((copy_157:float): float) = (-.) r  xk_147 in
                        let (l_149:float) = self.errork_139 in
                        self.errork_139 <- copy_157 ;
                        (let ((errorkm1_142:float): float) = l_149 in
                         let ((derivativek_133:float): float) =
                             (/.) ((-.) self.errork_139  errorkm1_142)  dt in
                         let (l_150:float) = self.integralk1_144 in
                         let ((integralk_143:float): float) = l_150 in
                         let ((derivativek1help_135:float): float) =
                             (+.) ((-.) (( *. ) (-2.)  self.errork_139) 
                                        integralk_143) 
                                  (( *. ) 0.5  derivativek_133) in
                         let ((integralk1help_145:float): float) =
                             (+.) ((+.) (( *. ) 0.08  self.errork_139) 
                                        (( *. ) 0.99  integralk_143)) 
                                  (( *. ) 0.005  derivativek_133) in
                         let ((errork1help_141:float): float) =
                             (+.) ((-.) (( *. ) 0.8  self.errork_139) 
                                        (( *. ) 0.1  integralk_143)) 
                                  (( *. ) 0.05  derivativek_133) in
                         let ((uk_146:float): float) =
                             (-.) ((+.) (( *. ) kp  self.errork_139) 
                                        (( *. ) ki  integralk_143)) 
                                  (( *. ) kd  derivativek_133) in
                         let ((copy_156:float): float) =
                             (+.) xk_147  (( *. ) uk_146  dt) in
                         self.xk1_148 <- copy_156 ;
                         (let ((errork1_140:float): float) =
                              (-.) r  self.xk1_148 in
                          let ((copy_155:float): float) =
                              (+.) integralk_143  (( *. ) errork1_140  dt) in
                          self.integralk1_144 <- copy_155 ;
                          (let ((diffenergy1_136:float): float) =
                               (+.) (( *. ) (( *. ) 1.1375  errork1_140) 
                                            errork1_140) 
                                    (( *. ) (( *. ) 1.25  self.integralk1_144)
                                             self.integralk1_144) in
                           let ((energyk1_138:float): float) =
                               (+.) (( *. ) (( *. ) 1.1375  errork1_140) 
                                            errork1_140) 
                                    (( *. ) (( *. ) 1.25  self.integralk1_144)
                                             self.integralk1_144) in
                           let ((energyk_137:float): float) =
                               (+.) ((+.) ((+.) (( *. ) (( *. ) 1.1375 
                                                                self.errork_139)
                                                         self.errork_139) 
                                                (( *. ) (( *. ) 1.25 
                                                                integralk_143)
                                                         integralk_143)) 
                                          (( *. ) (( *. ) 0.05 
                                                          derivativek_133) 
                                                  derivativek_133)) 
                                    (( *. ) (( *. ) 1.  self.errork_139) 
                                            integralk_143) in
                           let ((derivativek1_134:float): float) =
                               (/.) ((-.) errork1_140  self.errork_139)  dt in
                           let (derivativek_128:float) = derivativek_133 in
                           let (integralk_130:float) = integralk_143 in
                           let (errork_129:float) = self.errork_139 in
                           let (uk_131:float) = uk_146 in
                           let (xk_132:float) = xk_147 in
                           let _ = print_float xk_132 in
                           let _ = print_string "," in
                           let _ = print_float uk_131 in
                           let _ = print_string "," in
                           let _ = print_float errork_129 in
                           let _ = print_string "," in
                           let _ = print_float integralk_130 in
                           let _ = print_string "," in
                           let _ = print_float derivativek_128 in
                           self.result_122 <- print_newline ())))
                    | _ -> self.result_122 <- ()  end) ; self.result_122)) in
       cstate_158.horizon <- min cstate_158.horizon  self.h_127 ; result_163)):
    unit) in 
  let main_reset self  =
    ((self.i_125 <- true ;
      self.xk1_148 <- 0. ; self.errork_139 <- 1. ; self.integralk1_144 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
