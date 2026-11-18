(* The Zelus compiler, version 2.2-dev
  (2026-11-17-19:54) *)
open Ztypes
let r = 1.

let dt = 0.1

let kp = 2.

type ('c , 'b , 'a) _exec =
  { mutable major_40 : 'c ; mutable i_44 : 'b ; mutable x_43 : 'a }

let exec (cstate_60:Ztypes.cstate) = 
  
  let exec_alloc _ =
    cstate_60.cmax <- (+) cstate_60.cmax  1;
    { major_40 = false ; i_44 = (false:bool) ; x_43 = { pos = 42.; der = 0. } } in
  let exec_step self ((time_39:float) , ()) =
    ((let (cindex_61:int) = cstate_60.cindex in
      let cpos_63 = ref (cindex_61:int) in
      cstate_60.cindex <- (+) cstate_60.cindex  1 ;
      self.major_40 <- cstate_60.major ;
      (if cstate_60.major then
       for i_1 = cindex_61 to 0 do Zls.set cstate_60.dvec  i_1  0. done
       else ((self.x_43.pos <- Zls.get cstate_60.cvec  !cpos_63 ;
              cpos_63 := (+) !cpos_63  1))) ;
      (let (result_65:(float  * float  * float)) =
           (if self.i_44 then self.x_43.pos <- (0. : float)) ;
           self.i_44 <- false ;
           (let ((error_41:float): float) = (-.) r  self.x_43.pos in
            let ((u_42:float): float) = ( *. ) kp  error_41 in
            self.x_43.der <- ( *. ) kp  ((-.) r  self.x_43.pos) ;
            (self.x_43.pos , u_42 , error_41)) in
       cpos_63 := cindex_61 ;
       (if cstate_60.major then
        (((Zls.set cstate_60.cvec  !cpos_63  self.x_43.pos ;
           cpos_63 := (+) !cpos_63  1)))
        else (((Zls.set cstate_60.dvec  !cpos_63  self.x_43.der ;
                cpos_63 := (+) !cpos_63  1)))) ; result_65)):float *
                                                             float * float) in
   let exec_reset self  =
     (self.i_44 <- true:unit) in
  Node { alloc = exec_alloc; step = exec_step ; reset = exec_reset }
type ('f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_46 : 'f ;
    mutable h_59 : 'e ;
    mutable i_57 : 'd ;
    mutable h_55 : 'c ; mutable result_54 : 'b ; mutable x_53 : 'a }

let main (cstate_66:Ztypes.cstate) = 
  
  let main_alloc _ =
    cstate_66.cmax <- (+) cstate_66.cmax  1;
    { major_46 = false ;
      h_59 = 42. ;
      i_57 = (false:bool) ;
      h_55 = (42.:float) ;
      result_54 = (():unit) ; x_53 = { pos = 42.; der = 0. } } in
  let main_step self ((time_45:float) , ()) =
    ((let (cindex_67:int) = cstate_66.cindex in
      let cpos_69 = ref (cindex_67:int) in
      cstate_66.cindex <- (+) cstate_66.cindex  1 ;
      self.major_46 <- cstate_66.major ;
      (if cstate_66.major then
       for i_1 = cindex_67 to 0 do Zls.set cstate_66.dvec  i_1  0. done
       else ((self.x_53.pos <- Zls.get cstate_66.cvec  !cpos_69 ;
              cpos_69 := (+) !cpos_69  1))) ;
      (let (result_71:unit) =
           let h_58 = ref (infinity:float) in
           (if self.i_57 then self.h_55 <- (+.) time_45  0.) ;
           (let (z_56:bool) = (&&) self.major_46  ((>=) time_45  self.h_55) in
            self.h_55 <- (if z_56 then (+.) self.h_55  0.1 else self.h_55) ;
            h_58 := min !h_58  self.h_55 ;
            self.h_59 <- !h_58 ;
            (if self.i_57 then self.x_53.pos <- (0. : float)) ;
            self.i_57 <- false ;
            (let () = () in
             self.x_53.der <- ( *. ) kp  ((-.) r  self.x_53.pos) ;
             (let (x_50:float) = self.x_53.pos in
              let ((error_51:float): float) = (-.) r  self.x_53.pos in
              let ((u_52:float): float) = ( *. ) kp  error_51 in
              let (u_49:float) = u_52 in
              let (error_47:float) = error_51 in
              let (trigger_48:zero) = z_56 in
              (begin match trigger_48 with
                     | true ->
                         let _ = print_float x_50 in
                         let _ = print_string "," in
                         let _ = print_float u_49 in
                         let _ = print_string "," in
                         let _ = print_float error_47 in
                         let _ = print_string "," in
                         let _ = print_float r in
                         self.result_54 <- print_newline ()
                     | _ -> self.result_54 <- ()  end) ; self.result_54))) in
       cstate_66.horizon <- min cstate_66.horizon  self.h_59 ;
       cpos_69 := cindex_67 ;
       (if cstate_66.major then
        (((Zls.set cstate_66.cvec  !cpos_69  self.x_53.pos ;
           cpos_69 := (+) !cpos_69  1)))
        else (((Zls.set cstate_66.dvec  !cpos_69  self.x_53.der ;
                cpos_69 := (+) !cpos_69  1)))) ; result_71)):unit) in 
  let main_reset self  =
    (self.i_57 <- true:unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
