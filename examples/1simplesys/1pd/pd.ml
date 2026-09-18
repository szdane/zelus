(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let r = 1.

let kp = 2.

let kd = 0.5

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable m_82 : 'c ; mutable xk1_79 : 'b ; mutable errork_74 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { m_82 = (42.:float) ; xk1_79 = (42.:float) ; errork_74 = (42.:float) } in
  let exec_reset self  =
    ((self.xk1_79 <- 0. ; self.errork_74 <- 1. ; self.m_82 <- 1.):unit) in 
  let exec_step self () =
    ((let (l_81:float) = self.xk1_79 in
      let ((xk_78:float): float) = l_81 in
      let ((copy_111:float): float) = (-.) r  xk_78 in
      let (l_80:float) = self.errork_74 in
      self.errork_74 <- copy_111 ;
      (let (next_83:float) = self.m_82 in
       let ((energyk_73:float): float) = next_83 in
       let ((errorkm1_76:float): float) = l_80 in
       let ((derivativek_71:float): float) =
           (/.) ((-.) self.errork_74  errorkm1_76)  dt in
       self.m_82 <- (-.) ((-.) energyk_73 
                               (( *. ) (( *. ) 0.2  self.errork_74) 
                                       self.errork_74)) 
                         (( *. ) (( *. ) 0.0275  derivativek_71) 
                                 derivativek_71) ;
       (let ((uk_77:float): float) =
            (-.) (( *. ) kp  self.errork_74)  (( *. ) kd  derivativek_71) in
        let ((copy_110:float): float) = (+.) xk_78  (( *. ) uk_77  dt) in
        self.xk1_79 <- copy_110 ;
        (let ((errork1_75:float): float) = (-.) r  self.xk1_79 in
         let ((derivativek1_72:float): float) =
             (/.) ((-.) errork1_75  self.errork_74)  dt in
         (xk_78 , uk_77 , self.errork_74 , derivativek_71))))):float *
                                                               float *
                                                               float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_85 : 'h ;
    mutable h_92 : 'g ;
    mutable i_90 : 'f ;
    mutable h_88 : 'e ;
    mutable result_87 : 'd ;
    mutable m_108 : 'c ; mutable xk1_105 : 'b ; mutable errork_100 : 'a }

let main (cstate_114:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_85 = false ;
      h_92 = 42. ;
      i_90 = (false:bool) ;
      h_88 = (42.:float) ;
      result_87 = (():unit) ;
      m_108 = (42.:float) ; xk1_105 = (42.:float) ; errork_100 = (42.:float) } in
  let main_step self ((time_84:float) , ()) =
    ((self.major_85 <- cstate_114.major ;
      (let (result_119:unit) =
           let h_91 = ref (infinity:float) in
           (if self.i_90 then self.h_88 <- (+.) time_84  0.) ;
           (let (z_89:bool) = (&&) self.major_85  ((>=) time_84  self.h_88) in
            self.h_88 <- (if z_89 then (+.) self.h_88  0.1 else self.h_88) ;
            h_91 := min !h_91  self.h_88 ;
            self.h_92 <- !h_91 ;
            self.i_90 <- false ;
            (let (trigger_86:zero) = z_89 in
             (begin match trigger_86 with
                    | true ->
                        let () = () in
                        let (l_107:float) = self.xk1_105 in
                        let ((xk_104:float): float) = l_107 in
                        let ((copy_113:float): float) = (-.) r  xk_104 in
                        let (l_106:float) = self.errork_100 in
                        self.errork_100 <- copy_113 ;
                        (let (next_109:float) = self.m_108 in
                         let ((energyk_99:float): float) = next_109 in
                         let ((errorkm1_102:float): float) = l_106 in
                         let ((derivativek_97:float): float) =
                             (/.) ((-.) self.errork_100  errorkm1_102)  dt in
                         self.m_108 <- (-.) ((-.) energyk_99 
                                                  (( *. ) (( *. ) 0.2 
                                                                  self.errork_100)
                                                           self.errork_100)) 
                                            (( *. ) (( *. ) 0.0275 
                                                            derivativek_97) 
                                                    derivativek_97) ;
                         (let ((uk_103:float): float) =
                              (-.) (( *. ) kp  self.errork_100) 
                                   (( *. ) kd  derivativek_97) in
                          let ((copy_112:float): float) =
                              (+.) xk_104  (( *. ) uk_103  dt) in
                          self.xk1_105 <- copy_112 ;
                          (let ((errork1_101:float): float) =
                               (-.) r  self.xk1_105 in
                           let ((derivativek1_98:float): float) =
                               (/.) ((-.) errork1_101  self.errork_100)  dt in
                           let (derivative_93:float) = derivativek_97 in
                           let (error_94:float) = self.errork_100 in
                           let (u_95:float) = uk_103 in
                           let (x_96:float) = xk_104 in
                           let _ = print_float x_96 in
                           let _ = print_string "," in
                           let _ = print_float u_95 in
                           let _ = print_string "," in
                           let _ = print_float error_94 in
                           let _ = print_string "," in
                           let _ = print_float derivative_93 in
                           self.result_87 <- print_newline ())))
                    | _ -> self.result_87 <- ()  end) ; self.result_87)) in
       cstate_114.horizon <- min cstate_114.horizon  self.h_92 ; result_119)):
    unit) in 
  let main_reset self  =
    ((self.i_90 <- true ;
      self.xk1_105 <- 0. ; self.errork_100 <- 1. ; self.m_108 <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
