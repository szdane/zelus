(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let r = 1.

let kp = 2.

let kd = 0.5

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable xk1_98 : 'c ; mutable errork_93 : 'b ; mutable energyk1_91 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_98 = (42.:float) ;
      errork_93 = (42.:float) ; energyk1_91 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_98 <- 0. ; self.errork_93 <- 1. ; self.energyk1_91 <- 1.):
    unit) in 
  let exec_step self () =
    ((let (l_101:float) = self.xk1_98 in
      let ((xk_97:float): float) = l_101 in
      let ((copy_134:float): float) = (-.) r  xk_97 in
      let (l_100:float) = self.errork_93 in
      self.errork_93 <- copy_134 ;
      (let (l_99:float) = self.energyk1_91 in
       let ((energyk_90:float): float) = l_99 in
       let ((errorkm1_95:float): float) = l_100 in
       let ((derivativek_87:float): float) =
           (/.) ((-.) self.errork_93  errorkm1_95)  dt in
       let ((copy_132:float): float) =
           (-.) ((-.) energyk_90 
                      (( *. ) (( *. ) 0.2  self.errork_93)  self.errork_93)) 
                (( *. ) (( *. ) 0.0275  derivativek_87)  derivativek_87) in
       self.energyk1_91 <- copy_132 ;
       (let ((engerydec_92:float): float) = (-.) self.energyk1_91  energyk_90 in
        let ((diffenergy3_89:float): float) =
            (-.) (( *. ) (( *. ) (-0.2)  self.errork_93)  self.errork_93) 
                 (( *. ) (( *. ) 0.0275  derivativek_87)  derivativek_87) in
        let ((uk_96:float): float) =
            (-.) (( *. ) kp  self.errork_93)  (( *. ) kd  derivativek_87) in
        let ((copy_133:float): float) = (+.) xk_97  (( *. ) uk_96  dt) in
        self.xk1_98 <- copy_133 ;
        (let ((errork1_94:float): float) = (-.) r  self.xk1_98 in
         let ((derivativek1_88:float): float) =
             (/.) ((-.) errork1_94  self.errork_93)  dt in
         (xk_97 ,
          uk_96 ,
          self.errork_93 , derivativek_87 , energyk_90 , self.energyk1_91))))):
    float * float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_103 : 'h ;
    mutable h_110 : 'g ;
    mutable i_108 : 'f ;
    mutable h_106 : 'e ;
    mutable result_105 : 'd ;
    mutable xk1_128 : 'c ;
    mutable errork_123 : 'b ; mutable energyk1_121 : 'a }

let main (cstate_138:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_103 = false ;
      h_110 = 42. ;
      i_108 = (false:bool) ;
      h_106 = (42.:float) ;
      result_105 = (():unit) ;
      xk1_128 = (42.:float) ;
      errork_123 = (42.:float) ; energyk1_121 = (42.:float) } in
  let main_step self ((time_102:float) , ()) =
    ((self.major_103 <- cstate_138.major ;
      (let (result_143:unit) =
           let h_109 = ref (infinity:float) in
           (if self.i_108 then self.h_106 <- (+.) time_102  0.) ;
           (let (z_107:bool) =
                (&&) self.major_103  ((>=) time_102  self.h_106) in
            self.h_106 <- (if z_107 then (+.) self.h_106  0.1 else self.h_106)
            ;
            h_109 := min !h_109  self.h_106 ;
            self.h_110 <- !h_109 ;
            self.i_108 <- false ;
            (let (trigger_104:zero) = z_107 in
             (begin match trigger_104 with
                    | true ->
                        let () = () in
                        let (l_131:float) = self.xk1_128 in
                        let ((xk_127:float): float) = l_131 in
                        let ((copy_137:float): float) = (-.) r  xk_127 in
                        let (l_130:float) = self.errork_123 in
                        self.errork_123 <- copy_137 ;
                        (let (l_129:float) = self.energyk1_121 in
                         let ((energyk_120:float): float) = l_129 in
                         let ((errorkm1_125:float): float) = l_130 in
                         let ((derivativek_117:float): float) =
                             (/.) ((-.) self.errork_123  errorkm1_125)  dt in
                         let ((copy_135:float): float) =
                             (-.) ((-.) energyk_120 
                                        (( *. ) (( *. ) 0.2  self.errork_123)
                                                 self.errork_123)) 
                                  (( *. ) (( *. ) 0.0275  derivativek_117) 
                                          derivativek_117) in
                         self.energyk1_121 <- copy_135 ;
                         (let ((engerydec_122:float): float) =
                              (-.) self.energyk1_121  energyk_120 in
                          let ((diffenergy3_119:float): float) =
                              (-.) (( *. ) (( *. ) (-0.2)  self.errork_123) 
                                           self.errork_123) 
                                   (( *. ) (( *. ) 0.0275  derivativek_117) 
                                           derivativek_117) in
                          let ((uk_126:float): float) =
                              (-.) (( *. ) kp  self.errork_123) 
                                   (( *. ) kd  derivativek_117) in
                          let ((copy_136:float): float) =
                              (+.) xk_127  (( *. ) uk_126  dt) in
                          self.xk1_128 <- copy_136 ;
                          (let ((errork1_124:float): float) =
                               (-.) r  self.xk1_128 in
                           let ((derivativek1_118:float): float) =
                               (/.) ((-.) errork1_124  self.errork_123)  dt in
                           let (en0_112:float) = self.energyk1_121 in
                           let (energy0_113:float) = energyk_120 in
                           let (derivative_111:float) = derivativek_117 in
                           let (error_114:float) = self.errork_123 in
                           let (u_115:float) = uk_126 in
                           let (x_116:float) = xk_127 in
                           let _ = print_float x_116 in
                           let _ = print_string "," in
                           let _ = print_float u_115 in
                           let _ = print_string "," in
                           let _ = print_float error_114 in
                           let _ = print_string "," in
                           let _ = print_float derivative_111 in
                           let _ = print_string "," in
                           let _ = print_float energy0_113 in
                           let _ = print_string "," in
                           let _ = print_float en0_112 in
                           self.result_105 <- print_newline ())))
                    | _ -> self.result_105 <- ()  end) ; self.result_105)) in
       cstate_138.horizon <- min cstate_138.horizon  self.h_110 ; result_143)):
    unit) in 
  let main_reset self  =
    ((self.i_108 <- true ;
      self.xk1_128 <- 0. ; self.errork_123 <- 1. ; self.energyk1_121 <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
