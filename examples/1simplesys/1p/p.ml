(* The Zelus compiler, version 2.2-dev
  (2026-09-9-21:8) *)
open Ztypes
let r = 1.

let kp = 16.

let dt = 0.1

let eps = 0.1

let x_max = 2.

let x_bound ((xk_68:float): float) =
  let ((xk1_69:float): float) =
      (+.) xk_68  (( *. ) (( *. ) kp  ((-.) r  xk_68))  dt) in
  xk1_69

type ('a) _exec =
  { mutable xk1_78 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ xk1_78 = (42.:float) } in
  let exec_reset self  =
    (self.xk1_78 <- 0.:unit) in 
  let exec_step self () =
    ((let (l_79:float) = self.xk1_78 in
      let ((xk_77:float): float) = l_79 in
      let ((copy_102:float): float) = x_bound xk_77 in
      self.xk1_78 <- copy_102 ;
      (let ((bound_70:float): float) = self.xk1_78 in
       let ((errork1_72:float): float) = (-.) r  self.xk1_78 in
       let ((v3_76:float): float) = errork1_72 in
       let ((v2_75:float): float) = (-.) 1.  (( *. ) kp  dt) in
       let ((errork_71:float): float) = (-.) r  xk_77 in
       let ((v1_74:float): float) =
           ( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_71 in
       let ((uk_73:float): float) = ( *. ) kp  errork_71 in
       (xk_77 , uk_73 , errork_71))):float * float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_81 : 'f ;
    mutable h_88 : 'e ;
    mutable i_86 : 'd ;
    mutable h_84 : 'c ; mutable result_83 : 'b ; mutable xk1_100 : 'a }

let main (cstate_104:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_81 = false ;
      h_88 = 42. ;
      i_86 = (false:bool) ;
      h_84 = (42.:float) ; result_83 = (():unit) ; xk1_100 = (42.:float) } in
  let main_step self ((time_80:float) , ()) =
    ((self.major_81 <- cstate_104.major ;
      (let (result_109:unit) =
           let h_87 = ref (infinity:float) in
           (if self.i_86 then self.h_84 <- (+.) time_80  0.) ;
           (let (z_85:bool) = (&&) self.major_81  ((>=) time_80  self.h_84) in
            self.h_84 <- (if z_85 then (+.) self.h_84  0.1 else self.h_84) ;
            h_87 := min !h_87  self.h_84 ;
            self.h_88 <- !h_87 ;
            self.i_86 <- false ;
            (let (trigger_82:zero) = z_85 in
             (begin match trigger_82 with
                    | true ->
                        let () = () in
                        let (l_101:float) = self.xk1_100 in
                        let ((xk_99:float): float) = l_101 in
                        let ((copy_103:float): float) = x_bound xk_99 in
                        self.xk1_100 <- copy_103 ;
                        (let ((bound_92:float): float) = self.xk1_100 in
                         let ((errork1_94:float): float) =
                             (-.) r  self.xk1_100 in
                         let ((v3_98:float): float) = errork1_94 in
                         let ((v2_97:float): float) =
                             (-.) 1.  (( *. ) kp  dt) in
                         let ((errork_93:float): float) = (-.) r  xk_99 in
                         let ((v1_96:float): float) =
                             ( *. ) ((-.) 1.  (( *. ) kp  dt))  errork_93 in
                         let (error_89:float) = errork_93 in
                         let ((uk_95:float): float) = ( *. ) kp  errork_93 in
                         let (u_90:float) = uk_95 in
                         let (x_91:float) = xk_99 in
                         let _ = print_float x_91 in
                         let _ = print_string "," in
                         let _ = print_float u_90 in
                         let _ = print_string "," in
                         let _ = print_float error_89 in
                         self.result_83 <- print_newline ())
                    | _ -> self.result_83 <- ()  end) ; self.result_83)) in
       cstate_104.horizon <- min cstate_104.horizon  self.h_88 ; result_109)):
    unit) in 
  let main_reset self  =
    ((self.i_86 <- true ; self.xk1_100 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
