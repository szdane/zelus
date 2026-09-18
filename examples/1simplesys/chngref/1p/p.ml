(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let dt = 0.1

let kp = 2.

type ('c , 'b , 'a) _exec =
  { mutable xk1_82 : 'c ; mutable r_77 : 'b ; mutable counter_73 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_82 = (42.:float) ; r_77 = (42.:float) ; counter_73 = (42.:float) } in
  let exec_reset self  =
    ((self.counter_73 <- 0. ; self.r_77 <- 1. ; self.xk1_82 <- 0.):unit) in 
  let exec_step self () =
    ((let ((v2_80:float): float) = (-.) 1.  (( *. ) kp  dt) in
      let (l_83:float) = self.counter_73 in
      let (counterm1_74:float) = l_83 in
      self.counter_73 <- (if (>) ((+.) counterm1_74  1.)  5.
                          then 1.
                          else (+.) l_83  1.) ;
      (let (l_84:float) = self.r_77 in
       let ((copy_113:float): float) =
           if (=) self.counter_73  5. then (~-.) l_84 else l_84 in
       self.r_77 <- copy_113 ;
       (let (l_85:float) = self.xk1_82 in
        let ((xk_81:float): float) = l_85 in
        let ((errork_75:float): float) = (-.) self.r_77  xk_81 in
        let ((v1_79:float): float) =
            ( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_75 in
        let ((copy_112:float): float) =
            (+.) xk_81  (( *. ) (( *. ) kp  ((-.) self.r_77  xk_81))  dt) in
        self.xk1_82 <- copy_112 ;
        (let ((errork1_76:float): float) = (-.) self.r_77  self.xk1_82 in
         let ((uk_78:float): float) = ( *. ) kp  errork_75 in
         (xk_81 , uk_78 , self.counter_73 , self.r_77))))):float *
                                                           float *
                                                           float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_87 : 'h ;
    mutable h_94 : 'g ;
    mutable i_92 : 'f ;
    mutable h_90 : 'e ;
    mutable result_89 : 'd ;
    mutable xk1_108 : 'c ; mutable r_103 : 'b ; mutable counter_99 : 'a }

let main (cstate_116:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_87 = false ;
      h_94 = 42. ;
      i_92 = (false:bool) ;
      h_90 = (42.:float) ;
      result_89 = (():unit) ;
      xk1_108 = (42.:float) ; r_103 = (42.:float) ; counter_99 = (42.:float) } in
  let main_step self ((time_86:float) , ()) =
    ((self.major_87 <- cstate_116.major ;
      (let (result_121:unit) =
           let h_93 = ref (infinity:float) in
           (if self.i_92 then self.h_90 <- (+.) time_86  0.) ;
           (let (z_91:bool) = (&&) self.major_87  ((>=) time_86  self.h_90) in
            self.h_90 <- (if z_91 then (+.) self.h_90  0.1 else self.h_90) ;
            h_93 := min !h_93  self.h_90 ;
            self.h_94 <- !h_93 ;
            self.i_92 <- false ;
            (let (trigger_88:zero) = z_91 in
             (begin match trigger_88 with
                    | true ->
                        let () = () in
                        let ((v2_106:float): float) =
                            (-.) 1.  (( *. ) kp  dt) in
                        let (l_109:float) = self.counter_99 in
                        let (counterm1_100:float) = l_109 in
                        self.counter_99 <- (if (>) ((+.) counterm1_100  1.) 
                                                   5.
                                            then 1.
                                            else (+.) l_109  1.) ;
                        (let (l_110:float) = self.r_103 in
                         let ((copy_115:float): float) =
                             if (=) self.counter_99  5.
                             then (~-.) l_110
                             else l_110 in
                         self.r_103 <- copy_115 ;
                         (let (l_111:float) = self.xk1_108 in
                          let ((xk_107:float): float) = l_111 in
                          let ((errork_101:float): float) =
                              (-.) self.r_103  xk_107 in
                          let ((v1_105:float): float) =
                              ( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_101 in
                          let ((copy_114:float): float) =
                              (+.) xk_107 
                                   (( *. ) (( *. ) kp 
                                                   ((-.) self.r_103  xk_107))
                                            dt) in
                          self.xk1_108 <- copy_114 ;
                          (let ((errork1_102:float): float) =
                               (-.) self.r_103  self.xk1_108 in
                           let (r_96:float) = self.r_103 in
                           let (counter_95:float) = self.counter_99 in
                           let ((uk_104:float): float) =
                               ( *. ) kp  errork_101 in
                           let (u_97:float) = uk_104 in
                           let (x_98:float) = xk_107 in
                           let _ = print_float x_98 in
                           let _ = print_string "," in
                           let _ = print_float u_97 in
                           let _ = print_string "," in
                           let _ = print_float counter_95 in
                           let _ = print_string "," in
                           let _ = print_float r_96 in
                           self.result_89 <- print_newline ())))
                    | _ -> self.result_89 <- ()  end) ; self.result_89)) in
       cstate_116.horizon <- min cstate_116.horizon  self.h_94 ; result_121)):
    unit) in 
  let main_reset self  =
    ((self.i_92 <- true ;
      self.counter_99 <- 0. ; self.r_103 <- 1. ; self.xk1_108 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
