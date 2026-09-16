(* The Zelus compiler, version 2.2-dev
  (2026-09-16-15:25) *)
open Ztypes
type state__569 = Switch_Down_49 | Switch_Up_48 
type state__568 = Switch_True_45 | Switch_False_44 
type state__567 = Switch_True_41 | Switch_False_40 
type ('c , 'b , 'a) _switch =
  { mutable r_80 : 'c ; mutable s_79 : 'b ; mutable o_78 : 'a }

let switch  = 
  
  let switch_alloc _ =
    ();
    { r_80 = (false:bool) ;
      s_79 = (Switch_True_41:state__567) ; o_78 = (false:bool) } in
  let switch_reset self  =
    ((self.r_80 <- false ; self.s_79 <- Switch_False_40):unit) in 
  let switch_step self (i_77:bool) =
    (((begin match self.s_79 with
             | Switch_False_40 ->
                 (if self.r_80 then ()) ;
                 self.o_78 <- false ;
                 (begin match i_77 with
                        | true ->
                            self.r_80 <- true ; self.s_79 <- Switch_True_41
                        | _ -> self.r_80 <- false  end)
             | Switch_True_41 ->
                 (if self.r_80 then ()) ;
                 self.o_78 <- true ;
                 (begin match i_77 with
                        | true ->
                            self.r_80 <- true ; self.s_79 <- Switch_False_40
                        | _ -> self.r_80 <- false  end)
              end) ; self.o_78):bool) in
  Node { alloc = switch_alloc; reset = switch_reset ; step = switch_step }
type ('c , 'b , 'a) _switch_strong =
  { mutable r_84 : 'c ; mutable s_83 : 'b ; mutable o_82 : 'a }

let switch_strong  = 
  
  let switch_strong_alloc _ =
    ();
    { r_84 = (false:bool) ;
      s_83 = (Switch_True_45:state__568) ; o_82 = (false:bool) } in
  let switch_strong_reset self  =
    ((self.r_84 <- false ; self.s_83 <- Switch_False_44):unit) in 
  let switch_strong_step self (i_81:bool) =
    (((begin match self.s_83 with
             | Switch_False_44 ->
                 (if self.r_84 then ()) ;
                 (begin match i_81 with
                        | true ->
                            self.r_84 <- true ; self.s_83 <- Switch_True_45
                        | _ -> self.r_84 <- false  end)
             | Switch_True_45 ->
                 (if self.r_84 then ()) ;
                 (begin match i_81 with
                        | true ->
                            self.r_84 <- true ; self.s_83 <- Switch_False_44
                        | _ -> self.r_84 <- false  end)
              end) ;
      (begin match self.s_83 with
             | Switch_False_44 -> (if self.r_84 then ()) ; self.o_82 <- false
             | Switch_True_45 -> (if self.r_84 then ()) ; self.o_82 <- true  end)
      ; self.o_82):bool) in
  Node { alloc = switch_strong_alloc; reset = switch_strong_reset ;
                                      step = switch_strong_step }
type ('g , 'f , 'e , 'd , 'c , 'b , 'a) _two =
  { mutable r_88 : 'g ;
    mutable s_87 : 'f ;
    mutable o_86 : 'e ;
    mutable i_92 : 'd ;
    mutable m_89 : 'c ; mutable i_96 : 'b ; mutable m_93 : 'a }

let two  = 
  
  let two_alloc _ =
    ();
    { r_88 = (false:bool) ;
      s_87 = (Switch_Down_49:state__569) ;
      o_86 = (42:int) ;
      i_92 = (false:bool) ;
      m_89 = (42:int) ; i_96 = (false:bool) ; m_93 = (42:int) } in
  let two_reset self  =
    ((self.r_88 <- false ;
      self.s_87 <- Switch_Up_48 ; self.i_92 <- true ; self.i_96 <- true):
    unit) in 
  let two_step self (i_85:'a468) =
    (((begin match self.s_87 with
             | Switch_Up_48 ->
                 (if self.r_88 then self.i_92 <- true) ;
                 (let (next_90:int) = self.m_89 in
                  let (next_91:int) = if self.i_92 then 0 else (+) next_90  1 in
                  self.i_92 <- false ;
                  self.o_86 <- next_91 ;
                  self.m_89 <- self.o_86 ;
                  (begin match (=) self.o_86  5 with
                         | true ->
                             self.r_88 <- false ; self.s_87 <- Switch_Down_49
                         | _ -> self.r_88 <- false  end))
             | Switch_Down_49 ->
                 (if self.r_88 then self.i_96 <- true) ;
                 (let (next_94:int) = self.m_93 in
                  let (next_95:int) = if self.i_96 then 0 else (-) next_94  1 in
                  self.i_96 <- false ;
                  self.o_86 <- next_95 ;
                  self.m_93 <- self.o_86 ;
                  (begin match (=) self.o_86  (-5) with
                         | true ->
                             self.r_88 <- false ; self.s_87 <- Switch_Up_48
                         | _ -> self.r_88 <- false  end))
              end) ; self.o_86):int) in
  Node { alloc = two_alloc; reset = two_reset ; step = two_step }
type ('a) _main1 =
  { mutable i_110 : 'a }

let main1  = 
  let Node { alloc = i_110_alloc; step = i_110_step ; reset = i_110_reset } = switch_strong 
   in let main1_alloc _ =
        ();{ i_110 = i_110_alloc () (* discrete *)  } in
  let main1_reset self  =
    (i_110_reset self.i_110 :unit) in 
  let main1_step self () =
    ((let (i_97:int) = read_int () in
      let (i_98:bool) = not ((=) i_97  0) in
      let (o_99:bool) = i_110_step self.i_110 i_98 in
      let (next_100:unit) = print_string "false" in
      let (next_101:unit) = print_string "true" in
      let _ = if o_99 then next_101 else next_100 in
      print_string " "):unit) in
  Node { alloc = main1_alloc; reset = main1_reset ; step = main1_step }
type ('a) _main2 =
  { mutable i_111 : 'a }

let main2  = 
  let Node { alloc = i_111_alloc; step = i_111_step ; reset = i_111_reset } = two 
   in let main2_alloc _ =
        ();{ i_111 = i_111_alloc () (* discrete *)  } in
  let main2_reset self  =
    (i_111_reset self.i_111 :unit) in 
  let main2_step self () =
    ((let (i1_102:int) = read_int () in
      let (i_103:bool) = not ((=) i1_102  0) in
      let (o_104:int) = i_111_step self.i_111 i_103 in
      let _ = print_int o_104 in
      print_string " "):unit) in
  Node { alloc = main2_alloc; reset = main2_reset ; step = main2_step }
type ('a) _main =
  { mutable i_112 : 'a }

let main  = 
  let Node { alloc = i_112_alloc; step = i_112_step ; reset = i_112_reset } = switch_strong 
   in let main_alloc _ =
        ();{ i_112 = i_112_alloc () (* discrete *)  } in
  let main_reset self  =
    (i_112_reset self.i_112 :unit) in 
  let main_step self () =
    ((let () = () in
      let (i_105:int) = read_int () in
      let (i_106:bool) = not ((=) i_105  0) in
      let (o_107:bool) = i_112_step self.i_112 i_106 in
      let (next_108:unit) = print_string "false" in
      let (next_109:unit) = print_string "true" in
      let _ = if o_107 then next_109 else next_108 in
      print_string " "):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
