(* The Zelus compiler, version 2.2-dev
  (2026-07-7-23:5) *)
open Ztypes
type state__896 =
Watertank_delay_Delaystart_37
| Watertank_delay_Off_36 | Watertank_delay_On_35 
type state__895 =
Watertank_delay_Delaystart_27
| Watertank_delay_Off_26 | Watertank_delay_On_25 
let minlevel = 10.

let maxlevel = 20.

let outflow = (-0.25)

let margin = 1.

let maxdelay = 3.

let inflow = 1.

type ('e , 'd , 'c , 'b , 'a) _exec =
  { mutable r_59 : 'e ;
    mutable s_58 : 'd ;
    mutable netflow_55 : 'c ; mutable level_54 : 'b ; mutable delay_53 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { r_59 = (false:bool) ;
      s_58 = (Watertank_delay_Delaystart_27:state__895) ;
      netflow_55 = (42.:float) ;
      level_54 = (42.:float) ; delay_53 = (42.:float) } in
  let exec_reset self  =
    ((self.r_59 <- false ;
      self.s_58 <- Watertank_delay_On_25 ;
      self.delay_53 <- 0. ; self.level_54 <- 15. ; self.netflow_55 <- 0.):
    unit) in 
  let exec_step self () =
    ((let (l_56:float) = self.delay_53 in
      let (l_57:float) = self.level_54 in
      (begin match self.s_58 with
             | Watertank_delay_On_25 ->
                 (if self.r_59 then ()) ;
                 (begin match (&&) ((>=) l_57  ((-.) maxlevel  margin)) 
                                   ((=) l_56  0.) with
                        | true ->
                            self.r_59 <- true ;
                            self.s_58 <- Watertank_delay_Off_26
                        | _ -> self.r_59 <- false  end)
             | Watertank_delay_Off_26 ->
                 (if self.r_59 then ()) ;
                 (begin match (&&) ((<=) l_57 
                                         ((+.) ((-.) minlevel 
                                                     (( *. ) maxdelay 
                                                             outflow)) 
                                               margin))  ((=) l_56  0.) with
                        | true ->
                            self.r_59 <- true ;
                            self.s_58 <- Watertank_delay_Delaystart_27
                        | _ -> self.r_59 <- false  end)
             | Watertank_delay_Delaystart_27 ->
                 (if self.r_59 then ()) ;
                 (begin match (>) l_56  ((-.) maxdelay  1.) with
                        | true ->
                            self.r_59 <- true ;
                            self.s_58 <- Watertank_delay_On_25
                        | _ -> self.r_59 <- false  end)
              end) ;
      (begin match self.s_58 with
             | Watertank_delay_On_25 ->
                 (if self.r_59 then ()) ;
                 self.delay_53 <- 0. ;
                 self.netflow_55 <- (+.) inflow  outflow ;
                 self.level_54 <- (+.) l_57  self.netflow_55
             | Watertank_delay_Off_26 ->
                 (if self.r_59 then ()) ;
                 self.delay_53 <- 0. ;
                 self.netflow_55 <- outflow ;
                 self.level_54 <- (+.) l_57  self.netflow_55
             | Watertank_delay_Delaystart_27 ->
                 (if self.r_59 then ()) ;
                 self.delay_53 <- (+.) l_56  1. ;
                 self.netflow_55 <- outflow ;
                 self.level_54 <- (+.) l_57  self.netflow_55
              end) ;
      (self.level_54 ,
       ((+.) ((-.) minlevel  (( *. ) maxdelay  outflow))  margin))):float *
                                                                    float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('j , 'i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_61 : 'j ;
    mutable h_68 : 'i ;
    mutable i_66 : 'h ;
    mutable h_64 : 'g ;
    mutable result_63 : 'f ;
    mutable r_77 : 'e ;
    mutable s_76 : 'd ;
    mutable netflow_73 : 'c ; mutable level_72 : 'b ; mutable delay_71 : 'a }

let main (cstate_78:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_61 = false ;
      h_68 = 42. ;
      i_66 = (false:bool) ;
      h_64 = (42.:float) ;
      result_63 = (():unit) ;
      r_77 = (false:bool) ;
      s_76 = (Watertank_delay_Delaystart_37:state__896) ;
      netflow_73 = (42.:float) ;
      level_72 = (42.:float) ; delay_71 = (42.:float) } in
  let main_step self ((time_60:float) , ()) =
    ((self.major_61 <- cstate_78.major ;
      (let (result_83:unit) =
           let h_67 = ref (infinity:float) in
           (if self.i_66 then self.h_64 <- (+.) time_60  0.) ;
           (let (z_65:bool) = (&&) self.major_61  ((>=) time_60  self.h_64) in
            self.h_64 <- (if z_65 then (+.) self.h_64  0.1 else self.h_64) ;
            h_67 := min !h_67  self.h_64 ;
            self.h_68 <- !h_67 ;
            self.i_66 <- false ;
            (let (trigger_62:zero) = z_65 in
             (begin match trigger_62 with
                    | true ->
                        let () = () in
                        let (flow_69:float) =
                            (+.) ((-.) minlevel  (( *. ) maxdelay  outflow)) 
                                 margin in
                        let (l_74:float) = self.delay_71 in
                        let (l_75:float) = self.level_72 in
                        (begin match self.s_76 with
                               | Watertank_delay_On_35 ->
                                   (if self.r_77 then ()) ;
                                   (begin match (&&) ((>=) l_75 
                                                           ((-.) maxlevel 
                                                                 margin)) 
                                                     ((=) l_74  0.) with
                                          | true ->
                                              self.r_77 <- true ;
                                              self.s_76 <- Watertank_delay_Off_36
                                          | _ -> self.r_77 <- false  end)
                               | Watertank_delay_Off_36 ->
                                   (if self.r_77 then ()) ;
                                   (begin match (&&) ((<=) l_75 
                                                           ((+.) ((-.) 
                                                                    minlevel 
                                                                    (
                                                                    ( *. ) 
                                                                    maxdelay 
                                                                    outflow))
                                                                  margin)) 
                                                     ((=) l_74  0.) with
                                          | true ->
                                              self.r_77 <- true ;
                                              self.s_76 <- Watertank_delay_Delaystart_37
                                          | _ -> self.r_77 <- false  end)
                               | Watertank_delay_Delaystart_37 ->
                                   (if self.r_77 then ()) ;
                                   (begin match (>) l_74  ((-.) maxdelay  1.) with
                                          | true ->
                                              self.r_77 <- true ;
                                              self.s_76 <- Watertank_delay_On_35
                                          | _ -> self.r_77 <- false  end)
                                end) ;
                        (begin match self.s_76 with
                               | Watertank_delay_On_35 ->
                                   (if self.r_77 then ()) ;
                                   self.delay_71 <- 0. ;
                                   self.netflow_73 <- (+.) inflow  outflow ;
                                   self.level_72 <- (+.) l_75 
                                                         self.netflow_73
                               | Watertank_delay_Off_36 ->
                                   (if self.r_77 then ()) ;
                                   self.delay_71 <- 0. ;
                                   self.netflow_73 <- outflow ;
                                   self.level_72 <- (+.) l_75 
                                                         self.netflow_73
                               | Watertank_delay_Delaystart_37 ->
                                   (if self.r_77 then ()) ;
                                   self.delay_71 <- (+.) l_74  1. ;
                                   self.netflow_73 <- outflow ;
                                   self.level_72 <- (+.) l_75 
                                                         self.netflow_73
                                end) ;
                        (let (level_70:float) = self.level_72 in
                         let _ = print_float level_70 in
                         let _ = print_string ", " in
                         let _ = print_float flow_69 in
                         self.result_63 <- print_newline ())
                    | _ -> self.result_63 <- ()  end) ; self.result_63)) in
       cstate_78.horizon <- min cstate_78.horizon  self.h_68 ; result_83)):
    unit) in 
  let main_reset self  =
    ((self.i_66 <- true ;
      self.r_77 <- false ;
      self.s_76 <- Watertank_delay_On_35 ;
      self.delay_71 <- 0. ; self.level_72 <- 15. ; self.netflow_73 <- 0.):
    unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
