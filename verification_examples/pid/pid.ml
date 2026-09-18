(* The Zelus compiler, version 2.2-dev
  (2026-09-8-16:32) *)
open Ztypes
let r = 1.

let kp = 30.

let ki = 40.

let kd = 10.

let mass = 4.

let k = 15.

let b = 4.

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable xk1_75 : 'c ; mutable spdk1_72 : 'b ; mutable integralk_69 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_75 = (42.:float) ;
      spdk1_72 = (42.:float) ; integralk_69 = (42.:float) } in
  let exec_reset self  =
    ((self.spdk1_72 <- 0. ; self.xk1_75 <- 0. ; self.integralk_69 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_77:float) = self.spdk1_72 in
      let (spdk_71:float) = l_77 in
      let (l_78:float) = self.xk1_75 in
      let (xk_74:float) = l_78 in
      let ((copy_106:float): float) = (+.) xk_74  (( *. ) spdk_71  dt) in
      self.xk1_75 <- copy_106 ;
      (let (l_76:float) = self.integralk_69 in
       let (integralkm1_70:float) = l_76 in
       let ((errork_68:float): float) = (-.) r  xk_74 in
       let ((copy_104:float): float) =
           (+.) integralkm1_70  (( *. ) errork_68  dt) in
       self.integralk_69 <- copy_104 ;
       (let ((uk_73:float): float) =
            (-.) ((+.) (( *. ) kp  errork_68)  (( *. ) ki  self.integralk_69))
                  (( *. ) kd  spdk_71) in
        let ((copy_105:float): float) =
            (+.) spdk_71 
                 ((/.) (( *. ) ((+.) ((-.) (( *. ) ((~-.) k)  xk_74) 
                                           (( *. ) b  spdk_71))  uk_73)  
                               dt)  mass) in
        self.spdk1_72 <- copy_105 ;
        (xk_74 , uk_73 , errork_68 , self.integralk_69 , spdk_71)))):
    float * float * float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_80 : 'h ;
    mutable h_87 : 'g ;
    mutable i_85 : 'f ;
    mutable h_83 : 'e ;
    mutable result_82 : 'd ;
    mutable xk1_100 : 'c ; mutable spdk1_97 : 'b ; mutable integralk_94 : 'a }

let main (cstate_110:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_80 = false ;
      h_87 = 42. ;
      i_85 = (false:bool) ;
      h_83 = (42.:float) ;
      result_82 = (():unit) ;
      xk1_100 = (42.:float) ;
      spdk1_97 = (42.:float) ; integralk_94 = (42.:float) } in
  let main_step self ((time_79:float) , ()) =
    ((self.major_80 <- cstate_110.major ;
      (let (result_115:unit) =
           let h_86 = ref (infinity:float) in
           (if self.i_85 then self.h_83 <- (+.) time_79  0.) ;
           (let (z_84:bool) = (&&) self.major_80  ((>=) time_79  self.h_83) in
            self.h_83 <- (if z_84 then (+.) self.h_83  0.1 else self.h_83) ;
            h_86 := min !h_86  self.h_83 ;
            self.h_87 <- !h_86 ;
            self.i_85 <- false ;
            (let (trigger_81:zero) = z_84 in
             (begin match trigger_81 with
                    | true ->
                        let () = () in
                        let (l_102:float) = self.spdk1_97 in
                        let (spdk_96:float) = l_102 in
                        let (l_103:float) = self.xk1_100 in
                        let (xk_99:float) = l_103 in
                        let ((copy_109:float): float) =
                            (+.) xk_99  (( *. ) spdk_96  dt) in
                        self.xk1_100 <- copy_109 ;
                        (let (l_101:float) = self.integralk_94 in
                         let (integralkm1_95:float) = l_101 in
                         let ((errork_93:float): float) = (-.) r  xk_99 in
                         let ((copy_107:float): float) =
                             (+.) integralkm1_95  (( *. ) errork_93  dt) in
                         self.integralk_94 <- copy_107 ;
                         (let ((uk_98:float): float) =
                              (-.) ((+.) (( *. ) kp  errork_93) 
                                         (( *. ) ki  self.integralk_94)) 
                                   (( *. ) kd  spdk_96) in
                          let ((copy_108:float): float) =
                              (+.) spdk_96 
                                   ((/.) (( *. ) ((+.) ((-.) (( *. ) 
                                                                ((~-.) k) 
                                                                xk_99) 
                                                             (( *. ) 
                                                                b  spdk_96)) 
                                                       uk_98)  dt)  mass) in
                          self.spdk1_97 <- copy_108 ;
                          (let (derivativek_88:float) = spdk_96 in
                           let (integralk_90:float) = self.integralk_94 in
                           let (errork_89:float) = errork_93 in
                           let (uk_91:float) = uk_98 in
                           let (xk_92:float) = xk_99 in
                           let _ = print_float xk_92 in
                           let _ = print_string "," in
                           let _ = print_float uk_91 in
                           let _ = print_string "," in
                           let _ = print_float errork_89 in
                           let _ = print_string "," in
                           let _ = print_float integralk_90 in
                           let _ = print_string "," in
                           let _ = print_float derivativek_88 in
                           self.result_82 <- print_newline ())))
                    | _ -> self.result_82 <- ()  end) ; self.result_82)) in
       cstate_110.horizon <- min cstate_110.horizon  self.h_87 ; result_115)):
    unit) in 
  let main_reset self  =
    ((self.i_85 <- true ;
      self.spdk1_97 <- 0. ; self.xk1_100 <- 0. ; self.integralk_94 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
