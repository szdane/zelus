(* The Zelus compiler, version 2.2-dev
  (2025-11-14-2:53) *)
open Ztypes
type state__573 = Watertank_Down_29 | Watertank_Up_28 
type state__572 = Watertank_Down_21 | Watertank_Up_20 
let dt = 0.1

let maxflow = 0.5

let outflow = 0.1

let minlevel = 14.5

let maxlevel = 16.5

type ('d , 'c , 'b , 'a) _exec =
  { mutable r_50 : 'd ;
    mutable s_49 : 'c ; mutable level_46 : 'b ; mutable flow_45 : 'a }

let exec  = 
  
  let exec_alloc _ =
    ();
    { r_50 = (false:bool) ;
      s_49 = (Watertank_Down_21:state__572) ;
      level_46 = (42.:float) ; flow_45 = (42.:float) } in
  let exec_reset self  =
    ((self.r_50 <- false ;
      self.s_49 <- Watertank_Up_20 ;
      self.level_46 <- 15. ; self.flow_45 <- 0.):unit) in 
  let exec_step self () =
    ((let (l_48:float) = self.level_46 in
      (begin match self.s_49 with
             | Watertank_Up_20 ->
                 (if self.r_50 then ()) ;
                 (begin match (>=) l_48  ((-.) maxlevel  0.5) with
                        | true ->
                            self.r_50 <- true ;
                            self.s_49 <- Watertank_Down_21
                        | _ -> self.r_50 <- false  end)
             | Watertank_Down_21 ->
                 (if self.r_50 then ()) ;
                 (begin match (<=) l_48  ((+.) minlevel  0.5) with
                        | true ->
                            self.r_50 <- true ; self.s_49 <- Watertank_Up_20
                        | _ -> self.r_50 <- false  end)
              end) ;
      (let (l_47:float) = self.flow_45 in
       (begin match self.s_49 with
              | Watertank_Up_20 ->
                  (if self.r_50 then ()) ;
                  self.flow_45 <- maxflow ;
                  self.level_46 <- (+.) l_48 
                                        (( *. ) ((-.) l_47  outflow)  dt)
              | Watertank_Down_21 ->
                  (if self.r_50 then ()) ;
                  self.flow_45 <- 0. ;
                  self.level_46 <- (+.) l_48 
                                        (( *. ) ((-.) self.flow_45  outflow) 
                                                dt)
               end) ; (self.flow_45 , self.level_46))):float * float) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
type ('i , 'h , 'g , 'f , 'e , 'd , 'c , 'b , 'a) _main =
  { mutable major_52 : 'i ;
    mutable h_59 : 'h ;
    mutable i_57 : 'g ;
    mutable h_55 : 'f ;
    mutable result_54 : 'e ;
    mutable r_67 : 'd ;
    mutable s_66 : 'c ; mutable level_63 : 'b ; mutable flow_62 : 'a }

let main (cstate_68:Ztypes.cstate) = 
  
  let main_alloc _ =
    ();
    { major_52 = false ;
      h_59 = 42. ;
      i_57 = (false:bool) ;
      h_55 = (42.:float) ;
      result_54 = (():unit) ;
      r_67 = (false:bool) ;
      s_66 = (Watertank_Down_29:state__573) ;
      level_63 = (42.:float) ; flow_62 = (42.:float) } in
  let main_step self ((time_51:float) , ()) =
    ((self.major_52 <- cstate_68.major ;
      (let (result_73:unit) =
           let h_58 = ref (infinity:float) in
           (if self.i_57 then self.h_55 <- (+.) time_51  0.) ;
           (let (z_56:bool) = (&&) self.major_52  ((>=) time_51  self.h_55) in
            self.h_55 <- (if z_56 then (+.) self.h_55  dt else self.h_55) ;
            h_58 := min !h_58  self.h_55 ;
            self.h_59 <- !h_58 ;
            self.i_57 <- false ;
            (let (trigger_53:zero) = z_56 in
             (begin match trigger_53 with
                    | true ->
                        let () = () in
                        let (l_65:float) = self.level_63 in
                        (begin match self.s_66 with
                               | Watertank_Up_28 ->
                                   (if self.r_67 then ()) ;
                                   (begin match (>=) l_65 
                                                     ((-.) maxlevel  0.5) with
                                          | true ->
                                              self.r_67 <- true ;
                                              self.s_66 <- Watertank_Down_29
                                          | _ -> self.r_67 <- false  end)
                               | Watertank_Down_29 ->
                                   (if self.r_67 then ()) ;
                                   (begin match (<=) l_65 
                                                     ((+.) minlevel  0.5) with
                                          | true ->
                                              self.r_67 <- true ;
                                              self.s_66 <- Watertank_Up_28
                                          | _ -> self.r_67 <- false  end)
                                end) ;
                        (let (l_64:float) = self.flow_62 in
                         (begin match self.s_66 with
                                | Watertank_Up_28 ->
                                    (if self.r_67 then ()) ;
                                    self.flow_62 <- maxflow ;
                                    self.level_63 <- (+.) l_65 
                                                          (( *. ) ((-.) 
                                                                    l_64 
                                                                    outflow) 
                                                                  dt)
                                | Watertank_Down_29 ->
                                    (if self.r_67 then ()) ;
                                    self.flow_62 <- 0. ;
                                    self.level_63 <- (+.) l_65 
                                                          (( *. ) ((-.) 
                                                                    self.flow_62
                                                                     
                                                                    outflow) 
                                                                  dt)
                                 end) ;
                         (let (flow_60:float) = self.flow_62 in
                          let (level_61:float) = self.level_63 in
                          let _ = print_float level_61 in
                          let _ = print_string ", " in
                          let _ = print_float flow_60 in
                          self.result_54 <- print_newline ()))
                    | _ -> self.result_54 <- ()  end) ; self.result_54)) in
       cstate_68.horizon <- min cstate_68.horizon  self.h_59 ; result_73)):
    unit) in 
  let main_reset self  =
    ((self.i_57 <- true ;
      self.r_67 <- false ;
      self.s_66 <- Watertank_Up_28 ;
      self.level_63 <- 15. ; self.flow_62 <- 0.):unit) in
  Node { alloc = main_alloc; step = main_step ; reset = main_reset }
