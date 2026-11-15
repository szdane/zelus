(* The Zelus compiler, version 2.2-dev
  (2026-09-18-15:3) *)
open Ztypes
let dt = 0.1

let kp = 2.

type ('c , 'b , 'a) _exec =
  { mutable xk1_67 : 'c ; mutable r_64 : 'b ; mutable counter_61 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { xk1_67 = (42.:float) ; r_64 = (42.:float) ; counter_61 = (42.:float) } in
  let exec_reset self  =
    ((self.counter_61 <- 0. ; self.r_64 <- 1. ; self.xk1_67 <- 0.):unit) in 
  let exec_step self () =
    ((let (l_68:float) = self.counter_61 in
      let (counterm1_62:float) = l_68 in
      self.counter_61 <- (if (>) ((+.) counterm1_62  1.)  20.
                          then 1.
                          else (+.) l_68  1.) ;
      (let (l_69:float) = self.r_64 in
       let ((copy_95:float): float) =
           if (=) self.counter_61  20. then (~-.) l_69 else l_69 in
       self.r_64 <- copy_95 ;
       (let (l_70:float) = self.xk1_67 in
        let ((xk_66:float): float) = l_70 in
        let ((copy_94:float): float) =
            (+.) xk_66  (( *. ) (( *. ) kp  ((-.) self.r_64  xk_66))  dt) in
        self.xk1_67 <- copy_94 ;
        (let ((errork_63:float): float) = (-.) self.r_64  xk_66 in
         let ((uk_65:float): float) = ( *. ) kp  errork_63 in
         (xk_66 , uk_65 , self.counter_61 , self.r_64))))):float *
                                                           float *
                                                           float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_72 : 'h ;
    mutable h_79 : 'g ;
    mutable i_77 : 'f ;
    mutable h_75 : 'e ;
    mutable result_74 : 'd ;
    mutable xk1_90 : 'c ; mutable r_87 : 'b ; mutable counter_84 : 'a }

let main (cstate_98:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_72 = false ;
      h_79 = 42. ;
      i_77 = (false:bool) ;
      h_75 = (42.:float) ;
      result_74 = (():unit) ;
      xk1_90 = (42.:float) ; r_87 = (42.:float) ; counter_84 = (42.:float) } in
  let main_step self ((time_71:float) , ()) =
    ((self.major_72 <- cstate_98.major ;
      (let (result_103:unit) =
           let h_78 = ref (infinity:float) in
           (if self.i_77 then self.h_75 <- (+.) time_71  0.) ;
           (let (z_76:bool) = (&&) self.major_72  ((>=) time_71  self.h_75) in
            self.h_75 <- (if z_76 then (+.) self.h_75  0.1 else self.h_75) ;
            h_78 := min !h_78  self.h_75 ;
            self.h_79 <- !h_78 ;
            self.i_77 <- false ;
            (let (trigger_73:zero) = z_76 in
             (begin match trigger_73 with
                    | true ->
                        let () = () in
                        let (l_91:float) = self.counter_84 in
                        let (counterm1_85:float) = l_91 in
                        self.counter_84 <- (if (>) ((+.) counterm1_85  1.) 
                                                   20.
                                            then 1.
                                            else (+.) l_91  1.) ;
                        (let (l_92:float) = self.r_87 in
                         let ((copy_97:float): float) =
                             if (=) self.counter_84  20.
                             then (~-.) l_92
                             else l_92 in
                         self.r_87 <- copy_97 ;
                         (let (l_93:float) = self.xk1_90 in
                          let ((xk_89:float): float) = l_93 in
                          let ((copy_96:float): float) =
                              (+.) xk_89 
                                   (( *. ) (( *. ) kp 
                                                   ((-.) self.r_87  xk_89)) 
                                           dt) in
                          self.xk1_90 <- copy_96 ;
                          (let (r_81:float) = self.r_87 in
                           let (counter_80:float) = self.counter_84 in
                           let ((errork_86:float): float) =
                               (-.) self.r_87  xk_89 in
                           let ((uk_88:float): float) = ( *. ) kp  errork_86 in
                           let (u_82:float) = uk_88 in
                           let (x_83:float) = xk_89 in
                           let _ = print_float x_83 in
                           let _ = print_string "," in
                           let _ = print_float u_82 in
                           let _ = print_string "," in
                           let _ = print_float counter_80 in
                           let _ = print_string "," in
                           let _ = print_float r_81 in
                           self.result_74 <- print_newline ())))
                    | _ -> self.result_74 <- ()  end) ; self.result_74)) in
       cstate_98.horizon <- min cstate_98.horizon  self.h_79 ; result_103)):
    unit) in 
  let main_reset self  =
    ((self.i_77 <- true ;
      self.counter_84 <- 0. ; self.r_87 <- 1. ; self.xk1_90 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
