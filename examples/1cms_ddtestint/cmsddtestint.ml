(* The Zelus compiler, version 2.2-dev
  (2026-08-12-13:42) *)
open Ztypes
let setpoint = 1000

let sysuncertainty = 1

let m = ( * ) 1000  sysuncertainty

let k = ( * ) 20  sysuncertainty

let b = ( * ) 100  sysuncertainty

let piduncertainty = 1

let kp = ( * ) 10  piduncertainty

let ki = ( * ) 1  piduncertainty

let kd = ( * ) 1  piduncertainty

let dt = 1

let a1 = (-) ((/) (( * ) ((+) b  kd)  dt)  m)  3

let a2 = (+) 3 
             ((/) ((+) (( * ) (( * ) (-2)  ((+) b  kd))  dt) 
                       (( * ) (( * ) ((+) kp  k)  dt)  dt))  m)

let a3 = (-) ((/) ((+) ((-) (( * ) ((+) b  kd)  dt) 
                            (( * ) (( * ) ((+) kp  k)  dt)  dt)) 
                       (( * ) (( * ) (( * ) ki  dt)  dt)  dt))  m)  1

let stability_condition1 = a3

let stability_condition2 = (+) ((+) ((+) 1  a1)  a2)  a3

let stability_condition3 = (+) ((-) ((+) (-1)  a1)  a2)  a3

let stability_condition41 = (-) ((+) ((-) 1  (( * ) a3  a3))  (( * ) a1  a3))
                                 a2

let stability_condition42 = (+) ((-) ((-) 1  (( * ) a3  a3))  (( * ) a1  a3))
                                 a2

type ('b , 'a) _sys =
  { mutable x_76 : 'b ; mutable v_75 : 'a }

let sys  = 
   let sys_alloc _ =
     ();{ x_76 = (42:int) ; v_75 = (42:int) } in
  let sys_reset self  =
    ((self.x_76 <- 0 ; self.v_75 <- 0):unit) in 
  let sys_step self ((u_74:int): int) =
    ((let (l_77:int) = self.v_75 in
      let (l_78:int) = self.x_76 in
      let ((copy_111:int): int) = (+) l_78  (( * ) l_77  dt) in
      self.x_76 <- copy_111 ;
      (let ((copy_110:int): int) =
           (+) l_77 
               ((/) (( * ) ((+) ((-) (( * ) ((~-) k)  l_78)  (( * ) b  l_77))
                                 u_74)  dt)  m) in
       self.v_75 <- copy_110 ; (self.x_76 , self.v_75))):int * int) in
  Node { alloc = sys_alloc; reset = sys_reset ; step = sys_step }
type ('a) _pid =
  { mutable integral_antiwindup_82 : 'a }

let pid  = 
   let pid_alloc _ =
     ();{ integral_antiwindup_82 = (42:int) } in
  let pid_reset self  =
    (self.integral_antiwindup_82 <- 0:unit) in 
  let pid_step self (((x_80:int): int) , ((v_79:int): int)) =
    ((let ((error_81:int): int) = (-) setpoint  x_80 in
      let (l_85:int) = self.integral_antiwindup_82 in
      let ((copy_112:int): int) = (+) l_85  (( * ) dt  error_81) in
      self.integral_antiwindup_82 <- copy_112 ;
      (let ((u_83:int): int) =
           (-) ((+) (( * ) kp  error_81)  (( * ) ki  l_85))  (( * ) kd  v_79) in
       let ((u_sat_84:int): int) = u_83 in
       (error_81 , u_sat_84))):int * int) in
  Node { alloc = pid_alloc; reset = pid_reset ; step = pid_step }
type ('d , 'c , 'b , 'a) _exec =
  { mutable i_118 : 'd ;
    mutable i_117 : 'c ; mutable x_89 : 'b ; mutable v_88 : 'a }

let exec  = 
  let Node { alloc = i_118_alloc; step = i_118_step ; reset = i_118_reset } = pid 
   in 
  let Node { alloc = i_117_alloc; step = i_117_step ; reset = i_117_reset } = sys 
   in
  let exec_alloc _ =
    ();
    { x_89 = (42:int) ; v_88 = (42:int);
      i_118 = i_118_alloc () (* discrete *)  ;
      i_117 = i_117_alloc () (* discrete *)  } in
  let exec_reset self  =
    ((self.v_88 <- 0 ;
      self.x_89 <- 0 ; i_118_reset self.i_118  ; i_117_reset self.i_117 ):
    unit) in 
  let exec_step self () =
    ((let (l_90:int) = self.v_88 in
      let (l_91:int) = self.x_89 in
      let ((error_86:int) , (u_87:int)) = i_118_step self.i_118 (l_91 , l_90) in
      let ((copy_113:int) , (copy_114:int)) = i_117_step self.i_117 u_87 in
      self.x_89 <- copy_113 ;
      self.v_88 <- copy_114 ; (self.x_89 , self.v_88 , error_86 , u_87)):
    int * int * int * int) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable i_120 : 'i ;
    mutable i_119 : 'h ;
    mutable major_93 : 'g ;
    mutable h_100 : 'f ;
    mutable i_98 : 'e ;
    mutable h_96 : 'd ;
    mutable result_95 : 'c ; mutable x_107 : 'b ; mutable v_106 : 'a }

let main (cstate_121:Ztypes.cstate) = 
  let Node { alloc = i_120_alloc; step = i_120_step ; reset = i_120_reset } = pid 
   in 
  let Node { alloc = i_119_alloc; step = i_119_step ; reset = i_119_reset } = sys 
   in
  let main_alloc _ =
    ();
    { major_93 = false ;
      h_100 = 42. ;
      i_98 = (false:bool) ;
      h_96 = (42.:float) ;
      result_95 = (():unit) ; x_107 = (42:int) ; v_106 = (42:int);
      i_120 = i_120_alloc () (* discrete *)  ;
      i_119 = i_119_alloc () (* discrete *)  } in
  let main_step self ((time_92:float) , ()) =
    ((self.major_93 <- cstate_121.major ;
      (let (result_126:unit) =
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
                        let () = () in
                        let (l_108:int) = self.v_106 in
                        let (l_109:int) = self.x_107 in
                        let ((error_104:int) , (u_105:int)) =
                            i_120_step self.i_120 (l_109 , l_108) in
                        let _ = error_104 in
                        let (u_101:int) = u_105 in
                        let ((copy_115:int) , (copy_116:int)) =
                            i_119_step self.i_119 u_105 in
                        self.v_106 <- copy_116 ;
                        (let (v_102:int) = self.v_106 in
                         self.x_107 <- copy_115 ;
                         (let (x_103:int) = self.x_107 in
                          let _ = print_string "x= ," in
                          let _ = print_int x_103 in
                          let _ = print_string ", v= ," in
                          let _ = print_int v_102 in
                          let _ = print_string ", u= ," in
                          let _ = print_int u_101 in
                          self.result_95 <- print_newline ()))
                    | _ -> self.result_95 <- ()  end) ; self.result_95)) in
       cstate_121.horizon <- min cstate_121.horizon  self.h_100 ; result_126)):
    unit) in 
  let main_reset self  =
    ((self.i_98 <- true ;
      self.v_106 <- 0 ;
      self.x_107 <- 0 ; i_120_reset self.i_120  ; i_119_reset self.i_119 ):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
