(* The Zelus compiler, version 2.2-dev
  (2026-08-31-21:11) *)
open Ztypes
let r = 1.

let mass = 4.

let k = 15.

let b = 4.

let kp = 2.

let kd = 0.5

let dt = 0.1

type ('c , 'b , 'a) _exec =
  { mutable xk1_76 : 'c ; mutable spdk1_73 : 'b ; mutable errork_70 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_76 = (42.:float) ; spdk1_73 = (42.:float) ; errork_70 = (42.:float) } in
  let exec_reset self  =
    ((self.spdk1_73 <- 0. ; self.xk1_76 <- 0. ; self.errork_70 <- 1.):
    unit) in 
  let exec_step self () =
    ((let (l_79:float) = self.spdk1_73 in
      let ((spdk_72:float): float) = l_79 in
      let (l_80:float) = self.xk1_76 in
      let ((xk_75:float): float) = l_80 in
      let ((copy_108:float): float) = (+.) xk_75  (( *. ) spdk_72  dt) in
      self.xk1_76 <- copy_108 ;
      (let ((copy_106:float): float) = (-.) r  xk_75 in
       let (l_78:float) = self.errork_70 in
       self.errork_70 <- copy_106 ;
       (let ((errorkm1_71:float): float) = l_78 in
        let ((derivativek_69:float): float) =
            (/.) ((-.) self.errork_70  errorkm1_71)  dt in
        let ((uk_74:float): float) =
            (-.) (( *. ) kp  self.errork_70)  (( *. ) kd  derivativek_69) in
        let ((copy_107:float): float) =
            (+.) spdk_72 
                 ((/.) (( *. ) ((+.) ((-.) (( *. ) ((~-.) k)  xk_75) 
                                           (( *. ) b  spdk_72))  uk_74)  
                               dt)  mass) in
        self.spdk1_73 <- copy_107 ;
        (let ((xkm1_77:float): float) = (-.) r  errorkm1_71 in
         (xk_75 , uk_74 , self.errork_70 , derivativek_69))))):float *
                                                               float *
                                                               float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_82 : 'h ;
    mutable h_89 : 'g ;
    mutable i_87 : 'f ;
    mutable h_85 : 'e ;
    mutable result_84 : 'd ;
    mutable xk1_101 : 'c ; mutable spdk1_98 : 'b ; mutable errork_95 : 'a }

let main (cstate_112:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_82 = false ;
      h_89 = 42. ;
      i_87 = (false:bool) ;
      h_85 = (42.:float) ;
      result_84 = (():unit) ;
      xk1_101 = (42.:float) ;
      spdk1_98 = (42.:float) ; errork_95 = (42.:float) } in
  let main_step self ((time_81:float) , ()) =
    ((self.major_82 <- cstate_112.major ;
      (let (result_117:unit) =
           let h_88 = ref (infinity:float) in
           (if self.i_87 then self.h_85 <- (+.) time_81  0.) ;
           (let (z_86:bool) = (&&) self.major_82  ((>=) time_81  self.h_85) in
            self.h_85 <- (if z_86 then (+.) self.h_85  0.1 else self.h_85) ;
            h_88 := min !h_88  self.h_85 ;
            self.h_89 <- !h_88 ;
            self.i_87 <- false ;
            (let (trigger_83:zero) = z_86 in
             (begin match trigger_83 with
                    | true ->
                        let () = () in
                        let (l_104:float) = self.spdk1_98 in
                        let ((spdk_97:float): float) = l_104 in
                        let (l_105:float) = self.xk1_101 in
                        let ((xk_100:float): float) = l_105 in
                        let ((copy_111:float): float) =
                            (+.) xk_100  (( *. ) spdk_97  dt) in
                        self.xk1_101 <- copy_111 ;
                        (let ((copy_109:float): float) = (-.) r  xk_100 in
                         let (l_103:float) = self.errork_95 in
                         self.errork_95 <- copy_109 ;
                         (let ((errorkm1_96:float): float) = l_103 in
                          let ((derivativek_94:float): float) =
                              (/.) ((-.) self.errork_95  errorkm1_96)  dt in
                          let ((uk_99:float): float) =
                              (-.) (( *. ) kp  self.errork_95) 
                                   (( *. ) kd  derivativek_94) in
                          let ((copy_110:float): float) =
                              (+.) spdk_97 
                                   ((/.) (( *. ) ((+.) ((-.) (( *. ) 
                                                                ((~-.) k) 
                                                                xk_100) 
                                                             (( *. ) 
                                                                b  spdk_97)) 
                                                       uk_99)  dt)  mass) in
                          self.spdk1_98 <- copy_110 ;
                          (let ((xkm1_102:float): float) =
                               (-.) r  errorkm1_96 in
                           let (derivative_90:float) = derivativek_94 in
                           let (error_91:float) = self.errork_95 in
                           let (u_92:float) = uk_99 in
                           let (x_93:float) = xk_100 in
                           let _ = print_float x_93 in
                           let _ = print_string "," in
                           let _ = print_float u_92 in
                           let _ = print_string "," in
                           let _ = print_float error_91 in
                           let _ = print_string "," in
                           let _ = print_float derivative_90 in
                           self.result_84 <- print_newline ())))
                    | _ -> self.result_84 <- ()  end) ; self.result_84)) in
       cstate_112.horizon <- min cstate_112.horizon  self.h_89 ; result_117)):
    unit) in 
  let main_reset self  =
    ((self.i_87 <- true ;
      self.spdk1_98 <- 0. ; self.xk1_101 <- 0. ; self.errork_95 <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
