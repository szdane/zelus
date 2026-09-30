(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let r = 1.

let kp = 2.

let ki = 1.

let dt = 0.1

type ('d , 'c , 'b , 'a) _exec =
  { mutable xk1_83 : 'd ;
    mutable integralk1_80 : 'c ;
    mutable errork1_78 : 'b ; mutable energyk1_76 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_83 = (42.:float) ;
      integralk1_80 = (42.:float) ;
      errork1_78 = (42.:float) ; energyk1_76 = (42.:float) } in
  let exec_reset self  =
    ((self.integralk1_80 <- 0. ;
      self.errork1_78 <- 1. ; self.xk1_83 <- 0. ; self.energyk1_76 <- 0.99):
    unit) in 
  let exec_step self () =
    ((let (l_87:float) = self.integralk1_80 in
      let ((integralk_79:float): float) = l_87 in
      let (l_86:float) = self.errork1_78 in
      let ((errork_77:float): float) = l_86 in
      let ((uk_81:float): float) =
          (+.) (( *. ) kp  errork_77)  (( *. ) ki  integralk_79) in
      let (l_88:float) = self.xk1_83 in
      let ((xk_82:float): float) = l_88 in
      let ((copy_119:float): float) = (+.) xk_82  (( *. ) uk_81  dt) in
      self.xk1_83 <- copy_119 ;
      (let ((copy_118:float): float) = (-.) r  self.xk1_83 in
       self.errork1_78 <- copy_118 ;
       (let ((copy_117:float): float) =
            (+.) integralk_79  (( *. ) self.errork1_78  dt) in
        self.integralk1_80 <- copy_117 ;
        (let ((copy_116:float): float) =
             (+.) (( *. ) (( *. ) 0.99  self.errork1_78)  self.errork1_78) 
                  (( *. ) self.integralk1_80  self.integralk1_80) in
         let (l_85:float) = self.energyk1_76 in
         self.energyk1_76 <- copy_116 ;
         (let ((xkbound_84:float): float) = xk_82 in
          let ((energyk_75:float): float) = l_85 in
          (xk_82 , uk_81 , errork_77 , integralk_79)))))):float *
                                                          float *
                                                          float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_90 : 'i ;
    mutable h_97 : 'h ;
    mutable i_95 : 'g ;
    mutable h_93 : 'f ;
    mutable result_92 : 'e ;
    mutable xk1_110 : 'd ;
    mutable integralk1_107 : 'c ;
    mutable errork1_105 : 'b ; mutable energyk1_103 : 'a }

let main (cstate_124:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_90 = false ;
      h_97 = 42. ;
      i_95 = (false:bool) ;
      h_93 = (42.:float) ;
      result_92 = (():unit) ;
      xk1_110 = (42.:float) ;
      integralk1_107 = (42.:float) ;
      errork1_105 = (42.:float) ; energyk1_103 = (42.:float) } in
  let main_step self ((time_89:float) , ()) =
    ((self.major_90 <- cstate_124.major ;
      (let (result_129:unit) =
           let h_96 = ref (infinity:float) in
           (if self.i_95 then self.h_93 <- (+.) time_89  0.) ;
           (let (z_94:bool) = (&&) self.major_90  ((>=) time_89  self.h_93) in
            self.h_93 <- (if z_94 then (+.) self.h_93  0.1 else self.h_93) ;
            h_96 := min !h_96  self.h_93 ;
            self.h_97 <- !h_96 ;
            self.i_95 <- false ;
            (let (trigger_91:zero) = z_94 in
             (begin match trigger_91 with
                    | true ->
                        let () = () in
                        let (l_114:float) = self.integralk1_107 in
                        let ((integralk_106:float): float) = l_114 in
                        let (l_113:float) = self.errork1_105 in
                        let ((errork_104:float): float) = l_113 in
                        let ((uk_108:float): float) =
                            (+.) (( *. ) kp  errork_104) 
                                 (( *. ) ki  integralk_106) in
                        let (l_115:float) = self.xk1_110 in
                        let ((xk_109:float): float) = l_115 in
                        let ((copy_123:float): float) =
                            (+.) xk_109  (( *. ) uk_108  dt) in
                        self.xk1_110 <- copy_123 ;
                        (let ((copy_122:float): float) = (-.) r  self.xk1_110 in
                         self.errork1_105 <- copy_122 ;
                         (let ((copy_121:float): float) =
                              (+.) integralk_106 
                                   (( *. ) self.errork1_105  dt) in
                          self.integralk1_107 <- copy_121 ;
                          (let ((copy_120:float): float) =
                               (+.) (( *. ) (( *. ) 0.99  self.errork1_105) 
                                            self.errork1_105) 
                                    (( *. ) self.integralk1_107 
                                            self.integralk1_107) in
                           let (l_112:float) = self.energyk1_103 in
                           self.energyk1_103 <- copy_120 ;
                           (let ((xkbound_111:float): float) = xk_109 in
                            let ((energyk_102:float): float) = l_112 in
                            let (integralk_99:float) = integralk_106 in
                            let (errork_98:float) = errork_104 in
                            let (uk_100:float) = uk_108 in
                            let (xk_101:float) = xk_109 in
                            let _ = print_float xk_101 in
                            let _ = print_string "," in
                            let _ = print_float uk_100 in
                            let _ = print_string "," in
                            let _ = print_float errork_98 in
                            let _ = print_string "," in
                            let _ = print_float integralk_99 in
                            self.result_92 <- print_newline ()))))
                    | _ -> self.result_92 <- ()  end) ; self.result_92)) in
       cstate_124.horizon <- min cstate_124.horizon  self.h_97 ; result_129)):
    unit) in 
  let main_reset self  =
    ((self.i_95 <- true ;
      self.integralk1_107 <- 0. ;
      self.errork1_105 <- 1. ; self.xk1_110 <- 0. ; self.energyk1_103 <- 0.99):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
