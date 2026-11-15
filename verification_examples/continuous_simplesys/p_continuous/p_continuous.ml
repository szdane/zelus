(* The Zelus compiler, version 2.2-dev
  (2026-11-4-20:25) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

let pide ((x_83:float): float) =
  let ((error_84:float): float) = (-.) r  x_83 in
  let ((u_85:float): float) = ( *. ) kp  error_84 in
  error_84

let pidu ((x_86:float): float) =
  let ((error_87:float): float) = (-.) r  x_86 in
  let ((u_88:float): float) = ( *. ) kp  error_87 in
  u_88

type ('h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _exec =
  { mutable major_90 : 'h ;
    mutable h_105 : 'g ;
    mutable h_103 : 'f ;
    mutable i_101 : 'e ;
    mutable h_99 : 'd ;
    mutable result_96 : 'c ; mutable result_95 : 'b ; mutable x_94 : 'a }

let exec (cstate_130:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_130.cmax <- (+) cstate_130.cmax  1;
    { major_90 = false ;
      h_105 = 42. ;
      h_103 = (42.:float) ;
      i_101 = (false:bool) ;
      h_99 = (42.:float) ;
      result_96 = (42.:float) ;
      result_95 = (42.:float) ; x_94 = { pos = 42.; der = 0. } } in
  let exec_step self ((time_89:float) , ()) =
    ((let (cindex_131:int) = cstate_130.cindex in
      let cpos_133 = ref (cindex_131:int) in
      cstate_130.cindex <- (+) cstate_130.cindex  1 ;
      self.major_90 <- cstate_130.major ;
      (if cstate_130.major then
       for i_1 = cindex_131 to 0 do Zls.set cstate_130.dvec  i_1  0. done
       else ((self.x_94.pos <- Zls.get cstate_130.cvec  !cpos_133 ;
              cpos_133 := (+) !cpos_133  1))) ;
      (let (result_135:(float  * float  * float)) =
           let h_104 = ref (infinity:float) in
           let encore_102 = ref (false:bool) in
           let (l_98:float) = self.result_96 in
           (if self.i_101 then self.h_99 <- (+.) time_89  0.) ;
           (let (z_100:bool) = (&&) self.major_90  ((>=) time_89  self.h_99) in
            let (trigger_92:zero) = z_100 in
            (begin match trigger_92 with
                   | true ->
                       encore_102 := true ;
                       self.result_96 <- pidu self.x_94.pos | _ -> ()  end) ;
            (let (l_97:float) = self.result_95 in
             (begin match trigger_92 with
                    | true ->
                        encore_102 := true ;
                        self.result_95 <- pide self.x_94.pos | _ -> ()  end)
             ;
             self.h_103 <- (if !encore_102 then 0. else infinity) ;
             self.h_99 <- (if z_100 then (+.) self.h_99  dt else self.h_99) ;
             h_104 := min !h_104  (min self.h_103  self.h_99) ;
             self.h_105 <- !h_104 ;
             self.i_101 <- false ;
             (let (u_93:float) = self.result_96 in
              self.x_94.der <- u_93 ;
              (let (error_91:float) = self.result_95 in
               (self.x_94.pos , u_93 , error_91))))) in
       cstate_130.horizon <- min cstate_130.horizon  self.h_105 ;
       cpos_133 := cindex_131 ;
       (if cstate_130.major then
        (((Zls.set cstate_130.cvec  !cpos_133  self.x_94.pos ;
           cpos_133 := (+) !cpos_133  1)))
        else (((Zls.set cstate_130.dvec  !cpos_133  self.x_94.der ;
                cpos_133 := (+) !cpos_133  1)))) ; result_135)):float *
                                                                float * float) in
  
  let exec_reset self  =
    ((self.x_94.pos <- 0. ;
      self.result_96 <- 0. ; self.i_101 <- true ; self.result_95 <- 1.):
    unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_107 : 'j ;
    mutable h_129 : 'i ;
    mutable h_127 : 'h ;
    mutable i_125 : 'g ;
    mutable h_123 : 'f ;
    mutable h_121 : 'e ;
    mutable result_118 : 'd ;
    mutable result_117 : 'c ; mutable result_116 : 'b ; mutable x_115 : 'a }

let main (cstate_136:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_136.cmax <- (+) cstate_136.cmax  1;
    { major_107 = false ;
      h_129 = 42. ;
      h_127 = (42.:float) ;
      i_125 = (false:bool) ;
      h_123 = (42.:float) ;
      h_121 = (42.:float) ;
      result_118 = (():unit) ;
      result_117 = (42.:float) ;
      result_116 = (42.:float) ; x_115 = { pos = 42.; der = 0. } } in
  let main_step self ((time_106:float) , ()) =
    ((let (cindex_137:int) = cstate_136.cindex in
      let cpos_139 = ref (cindex_137:int) in
      cstate_136.cindex <- (+) cstate_136.cindex  1 ;
      self.major_107 <- cstate_136.major ;
      (if cstate_136.major then
       for i_1 = cindex_137 to 0 do Zls.set cstate_136.dvec  i_1  0. done
       else ((self.x_115.pos <- Zls.get cstate_136.cvec  !cpos_139 ;
              cpos_139 := (+) !cpos_139  1))) ;
      (let (result_141:unit) =
           let h_128 = ref (infinity:float) in
           let encore_126 = ref (false:bool) in
           let (l_120:float) = self.result_117 in
           (if self.i_125 then self.h_123 <- (+.) time_106  0.) ;
           (let (z_124:bool) =
                (&&) self.major_107  ((>=) time_106  self.h_123) in
            let (trigger_113:zero) = z_124 in
            (begin match trigger_113 with
                   | true ->
                       encore_126 := true ;
                       self.result_117 <- pidu self.x_115.pos | _ -> ()  end)
            ;
            (let (l_119:float) = self.result_116 in
             (begin match trigger_113 with
                    | true ->
                        encore_126 := true ;
                        self.result_116 <- pide self.x_115.pos | _ -> ()  end)
             ;
             self.h_127 <- (if !encore_126 then 0. else infinity) ;
             self.h_123 <- (if z_124 then (+.) self.h_123  dt else self.h_123)
             ;
             (if self.i_125 then self.h_121 <- (+.) time_106  0.) ;
             (let (z_122:bool) =
                  (&&) self.major_107  ((>=) time_106  self.h_121) in
              self.h_121 <- (if z_122
                             then (+.) self.h_121  0.1
                             else self.h_121) ;
              h_128 := min !h_128 
                           (min (min self.h_127  self.h_123)  self.h_121) ;
              self.h_129 <- !h_128 ;
              self.i_125 <- false ;
              (let () = () in
               let (u_114:float) = self.result_117 in
               self.x_115.der <- u_114 ;
               (let (x_111:float) = self.x_115.pos in
                let (u_110:float) = u_114 in
                let (error_112:float) = self.result_116 in
                let (error_108:float) = error_112 in
                let (trigger_109:zero) = z_122 in
                (begin match trigger_109 with
                       | true ->
                           let _ = print_float x_111 in
                           let _ = print_string "," in
                           let _ = print_float u_110 in
                           let _ = print_string "," in
                           let _ = print_float error_108 in
                           self.result_118 <- print_newline ()
                       | _ -> self.result_118 <- ()  end) ; self.result_118))))) in
       cstate_136.horizon <- min cstate_136.horizon  self.h_129 ;
       cpos_139 := cindex_137 ;
       (if cstate_136.major then
        (((Zls.set cstate_136.cvec  !cpos_139  self.x_115.pos ;
           cpos_139 := (+) !cpos_139  1)))
        else (((Zls.set cstate_136.dvec  !cpos_139  self.x_115.der ;
                cpos_139 := (+) !cpos_139  1)))) ; result_141)):unit) in 
  let main_reset self  =
    ((self.x_115.pos <- 0. ;
      self.result_117 <- 0. ; self.i_125 <- true ; self.result_116 <- 1.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
