(* The Zelus compiler, version 2.2-dev
  (2026-03-30-0:4) *)
open Ztypes
type state__555 = Watertank_Down_29 | Watertank_Up_28 
type state__554 = Watertank_Down_21 | Watertank_Up_20 
let dt = 0.1

let maxflow = 0.5

let outflow = 0.1

let minlevel = 14.5

let maxlevel = 16.5

type ('d , 'c , 'b , 'a) _exec =
  { mutable r_47 : 'd ;
    mutable s_46 : 'c ; mutable level_44 : 'b ; mutable flow_43 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { r_47 = (false:bool) ;
      s_46 = (Watertank_Down_21:state__554) ;
      level_44 = (42.:float) ; flow_43 = (42.:float) } in
  let exec_reset self  =
    ((self.r_47 <- false ;
      self.s_46 <- Watertank_Up_20 ;
      self.level_44 <- 15. ; self.flow_43 <- 0.):unit) in 
  let exec_step self () =
    ((let (l_45:float) = self.level_44 in
      (begin match self.s_46 with
             | Watertank_Up_20 ->
                 (if self.r_47 then ()) ;
                 (begin match (>=) l_45  ((-.) maxlevel  0.5) with
                        | true ->
                            self.r_47 <- true ;
                            self.s_46 <- Watertank_Down_21
                        | _ -> self.r_47 <- false  end)
             | Watertank_Down_21 ->
                 (if self.r_47 then ()) ;
                 (begin match (<=) l_45  ((+.) minlevel  0.5) with
                        | true ->
                            self.r_47 <- true ; self.s_46 <- Watertank_Up_20
                        | _ -> self.r_47 <- false  end)
              end) ;
      (begin match self.s_46 with
             | Watertank_Up_20 ->
                 (if self.r_47 then ()) ;
                 self.flow_43 <- maxflow ;
                 self.level_44 <- (+.) l_45 
                                       (( *. ) ((-.) maxflow  outflow)  dt)
             | Watertank_Down_21 ->
                 (if self.r_47 then ()) ;
                 self.flow_43 <- 0. ;
                 self.level_44 <- (+.) l_45  (( *. ) ((-.) 0.  outflow)  dt)
              end) ; (self.flow_43 , self.level_44)):float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_49 : 'i ;
    mutable h_56 : 'h ;
    mutable i_54 : 'g ;
    mutable h_52 : 'f ;
    mutable result_51 : 'e ;
    mutable r_63 : 'd ;
    mutable s_62 : 'c ; mutable level_60 : 'b ; mutable flow_59 : 'a }

let main (cstate_64:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_49 = false ;
      h_56 = 42. ;
      i_54 = (false:bool) ;
      h_52 = (42.:float) ;
      result_51 = (():unit) ;
      r_63 = (false:bool) ;
      s_62 = (Watertank_Down_29:state__555) ;
      level_60 = (42.:float) ; flow_59 = (42.:float) } in
  let main_step self ((time_48:float) , ()) =
    ((self.major_49 <- cstate_64.major ;
      (let (result_69:unit) =
           let h_55 = ref (infinity:float) in
           (if self.i_54 then self.h_52 <- (+.) time_48  0.) ;
           (let (z_53:bool) = (&&) self.major_49  ((>=) time_48  self.h_52) in
            self.h_52 <- (if z_53 then (+.) self.h_52  dt else self.h_52) ;
            h_55 := min !h_55  self.h_52 ;
            self.h_56 <- !h_55 ;
            self.i_54 <- false ;
            (let (trigger_50:zero) = z_53 in
             (begin match trigger_50 with
                    | true ->
                        let () = () in
                        let (l_61:float) = self.level_60 in
                        (begin match self.s_62 with
                               | Watertank_Up_28 ->
                                   (if self.r_63 then ()) ;
                                   (begin match (>=) l_61 
                                                     ((-.) maxlevel  0.5) with
                                          | true ->
                                              self.r_63 <- true ;
                                              self.s_62 <- Watertank_Down_29
                                          | _ -> self.r_63 <- false  end)
                               | Watertank_Down_29 ->
                                   (if self.r_63 then ()) ;
                                   (begin match (<=) l_61 
                                                     ((+.) minlevel  0.5) with
                                          | true ->
                                              self.r_63 <- true ;
                                              self.s_62 <- Watertank_Up_28
                                          | _ -> self.r_63 <- false  end)
                                end) ;
                        (begin match self.s_62 with
                               | Watertank_Up_28 ->
                                   (if self.r_63 then ()) ;
                                   self.flow_59 <- maxflow ;
                                   self.level_60 <- (+.) l_61 
                                                         (( *. ) ((-.) 
                                                                    maxflow 
                                                                    outflow) 
                                                                 dt)
                               | Watertank_Down_29 ->
                                   (if self.r_63 then ()) ;
                                   self.flow_59 <- 0. ;
                                   self.level_60 <- (+.) l_61 
                                                         (( *. ) ((-.) 
                                                                    0. 
                                                                    outflow) 
                                                                 dt)
                                end) ;
                        (let (flow_57:float) = self.flow_59 in
                         let (level_58:float) = self.level_60 in
                         let _ = print_float level_58 in
                         let _ = print_string ", " in
                         let _ = print_float flow_57 in
                         self.result_51 <- print_newline ())
                    | _ -> self.result_51 <- ()  end) ; self.result_51)) in
       cstate_64.horizon <- min cstate_64.horizon  self.h_56 ; result_69)):
    unit) in 
  let main_reset self  =
    ((self.i_54 <- true ;
      self.r_63 <- false ;
      self.s_62 <- Watertank_Up_28 ;
      self.level_60 <- 15. ; self.flow_59 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
