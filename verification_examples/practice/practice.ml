(* The Zelus compiler, version 2.2-dev
  (2026-11-18-19:55) *)
open Ztypes
type ('a) _exec =
  { mutable xk1_74 : 'a }

let exec  = 
   let exec_alloc _ =
     ();{ xk1_74 = (42.:float) } in
  let exec_reset self  =
    (self.xk1_74 <- 0.:unit) in 
  let exec_step self () =
    ((let (l_75:float) = self.xk1_74 in
      let ((xk_73:float): float) = l_75 in
      let ((copy_98:float): float) = (-.) (abs_float xk_73)  1. in
      self.xk1_74 <- copy_98 ;
      (let ((g_70:float): float) = 3. in
       let ((i_72:float): float) = ( ** ) (-2.)  g_70 in
       let ((h_71:float): float) = abs_float i_72 in
       let ((d_67:float): float) = (-1.) in
       let ((f_69:float): float) = abs_float d_67 in
       let ((b_65:float): float) = 1. in
       let ((c_66:float): float) = abs_float b_65 in
       let ((a_64:float): float) = 1. in
       let ((e_68:float): float) = 0.5 in
       a_64)):float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_77 : 'f ;
    mutable h_84 : 'e ;
    mutable i_82 : 'd ;
    mutable h_80 : 'c ; mutable result_79 : 'b ; mutable xk1_96 : 'a }

let main (cstate_100:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_77 = false ;
      h_84 = 42. ;
      i_82 = (false:bool) ;
      h_80 = (42.:float) ; result_79 = (():unit) ; xk1_96 = (42.:float) } in
  let main_step self ((time_76:float) , ()) =
    ((self.major_77 <- cstate_100.major ;
      (let (result_105:unit) =
           let h_83 = ref (infinity:float) in
           (if self.i_82 then self.h_80 <- (+.) time_76  0.) ;
           (let (z_81:bool) = (&&) self.major_77  ((>=) time_76  self.h_80) in
            self.h_80 <- (if z_81 then (+.) self.h_80  0.1 else self.h_80) ;
            h_83 := min !h_83  self.h_80 ;
            self.h_84 <- !h_83 ;
            self.i_82 <- false ;
            (let (trigger_78:zero) = z_81 in
             (begin match trigger_78 with
                    | true ->
                        let () = () in
                        let (l_97:float) = self.xk1_96 in
                        let ((xk_95:float): float) = l_97 in
                        let ((copy_99:float): float) =
                            (-.) (abs_float xk_95)  1. in
                        self.xk1_96 <- copy_99 ;
                        (let ((g_92:float): float) = 3. in
                         let ((i_94:float): float) = ( ** ) (-2.)  g_92 in
                         let ((h_93:float): float) = abs_float i_94 in
                         let ((d_89:float): float) = (-1.) in
                         let ((f_91:float): float) = abs_float d_89 in
                         let ((b_87:float): float) = 1. in
                         let ((c_88:float): float) = abs_float b_87 in
                         let ((e_90:float): float) = 0.5 in
                         let ((a_86:float): float) = 1. in
                         let (x_85:float) = a_86 in
                         let _ = print_float x_85 in
                         self.result_79 <- print_newline ())
                    | _ -> self.result_79 <- ()  end) ; self.result_79)) in
       cstate_100.horizon <- min cstate_100.horizon  self.h_84 ; result_105)):
    unit) in 
  let main_reset self  =
    ((self.i_82 <- true ; self.xk1_96 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
