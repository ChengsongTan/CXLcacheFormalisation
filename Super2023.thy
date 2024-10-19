(*   
     adapted from Sketch_and_Explore.thy by Florian Haftmann
*)

chapter \<open>Experimental commands \<^text>\<open>sketch\<close> and \<^text>\<open>explore\<close>\<close>

theory Super2023
  imports Main \<comment> \<open>TODO: generalize existing sledgehammer functions to Pure\<close>
  keywords "sketch" "explore" "sketch_subgoals" "super_sketch" "super_sketch3" "super_sketch3p" "super_sketch2b" "super_sketch2bp" "nsketch" :: diag
begin


ML_file "SC2023.ML"
            

ML \<open>
open ATP_Util
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_SMT
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh

open Sledgehammer_Commands1





open Subgoal
open Binding


fun createList(start, ending) = 
  if start = ending then []
  else start :: createList(start + 1, ending);

fun createList'(ending) =
  createList(1, ending + 1);

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
    val assms = Logic.strip_imp_prems horn;
    val concl = Logic.strip_imp_concl horn;
  in (fixes, assms, concl) end;

fun maybe_quote ctxt =
  ATP_Util.maybe_quote (Thy_Header.get_keywords' ctxt);

fun print_typ ctxt T =
  T
  |> Syntax.string_of_typ ctxt
  |> maybe_quote ctxt;

fun print_term ctxt t =
  t
  |> singleton (Syntax.uncheck_terms ctxt)
  |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt
      \<comment> \<open>TODO pointless to annotate explicit fixes in term\<close>
  |> Print_Mode.setmp [] (Syntax.unparse_term ctxt #> Pretty.string_of)
  |> Sledgehammer_Util.simplify_spaces
  |> maybe_quote ctxt;

fun eigen_context_for_statement (fixes, assms, concl) ctxt =
  let
    val (fixes', ctxt') = Variable.add_fixes (map fst fixes) ctxt;
    val subst_free = AList.lookup (op =) (map fst fixes ~~ fixes')
    val subst = map_aterms (fn Free (v, T) => Free (the_default v (subst_free v), T)
      | t => t)
    val assms' = map subst assms;
    val concl' = subst concl;
  in ((fixes, assms', concl'), ctxt') end;

fun print_isar_skeleton ctxt indent keyword stmt =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (print_term ctxt') assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));
    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [prefix ^ "  " ^ (if is_none if_s then "" else "using that ") ^ "sorry"]);
  in
    s
  end;

fun print_skeleton ctxt indent keyword stmt =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val prefix_sep = "\n" ^ prefix ^ "  and ";
    val show_s = prefix ^ keyword ^ " " ^ print_term ctxt' concl;
    val assumes_s = if null assms then NONE
      else SOME (prefix ^ "assume " ^ space_implode prefix_sep
        (map (print_term ctxt') assms));
    val fixes_s = if null fixes then NONE
      else SOME (prefix ^ "fix " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));
    val s = cat_lines (map_filter I [fixes_s, assumes_s] @ [show_s] @ [prefix ^ " sorry"]);
  in
    s
  end;

fun print_sketch ctxt method_text clauses =
  "proof" ^ method_text :: separate "next" (map (print_skeleton ctxt 2 "show") clauses) @ ["qed"];

fun print_numbered_isar_skeleton ctxt indent keyword stmt i state  =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term ctxt' t ) assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));


  

    val message1 = ( "sorry");


    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;



fun print_numbered_sketch  ctxt method_text1 clauses state =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: map (fn (stmt, i) => print_numbered_isar_skeleton ctxt 2 "show" stmt i state) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

fun not_needed i = (if i <= 20 andalso i >= 18 orelse i <= 47 andalso i >= 42 orelse i <= 66 andalso i >= 51 orelse  i >= 68 andalso i <= 199 andalso i <> 84 andalso i <> 135 orelse 
  i = 202 orelse i = 203 orelse i >= 205 andalso i <= 206 orelse i >= 208 andalso i <= 209 orelse i = 213 orelse i = 214 orelse i >= 216 andalso i <= 220 orelse
i >= 222 andalso i <= 234 orelse i >= 236 andalso i <= 237 orelse i >= 241 andalso i < 360 andalso i <> 249 orelse i > 360 then true else false) 


fun print_exploration ctxt method_text [clause] =
    ["proof -", print_isar_skeleton ctxt 2 "have" clause,
      "  then show ?thesis", "    by" ^ method_text, "qed"]
  | print_exploration ctxt method_text (clause :: clauses) =
    "proof -" :: print_isar_skeleton ctxt 2 "have" clause
      :: map (print_isar_skeleton ctxt 2 "moreover have") clauses
      @ ["  ultimately show ?thesis", "    by" ^ method_text, "qed"];

fun print_subgoal apply_line_opt (is_prems, is_for, is_sh) ctxt indent stmt =
  let
    val ((fixes, _, _), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val fixes_s =
      if not is_for orelse null fixes then NONE
      else SOME ("for " ^ space_implode " "
        (map (fn (v, _) => Proof_Context.print_name ctxt' v) fixes));
    val premises_s = if is_prems then SOME "premises prems" else NONE;
    val sh_s = if is_sh then SOME "sledgehammer" else NONE;
    val subgoal_s = map_filter I [SOME "subgoal", premises_s, fixes_s]
      |> space_implode " ";
    val using_s = if is_prems then SOME "using prems" else NONE;
    val s = cat_lines (
      [subgoal_s]
      @ map_filter (Option.map (fn s => prefix ^ s)) [using_s, apply_line_opt, sh_s]
      @ [prefix ^ "sorry"]);
  in
    s
  end;

fun coalesce_method_txt [] = ""
  | coalesce_method_txt [s] = s
  | coalesce_method_txt (s1 :: s2 :: ss) =
      if s1 = "(" orelse s1 = "["
        orelse s2 = ")" orelse s2 = "]" orelse s2= ":"
      then s1 ^ coalesce_method_txt (s2 :: ss)
      else s1 ^ " " ^ coalesce_method_txt (s2 :: ss);

fun print_subgoals options apply_line_opt ctxt _ clauses =
  separate "" (map (print_subgoal apply_line_opt options ctxt 2) clauses) @ ["done"];

fun print_proof_text_from_state print (some_method_ref : ((Method.text * Position.range) * Token.T list) option) state =
  let
    val state' = state
      |> Proof.proof (Option.map fst some_method_ref)
      |> Seq.the_result ""

    val { context = ctxt, facts = _, goal } = Proof.goal state';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text = case some_method_ref of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>
    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;
    val lines = if null clauses then
      if is_none some_method_ref then ["  .."]
      else ["  by" ^ method_text]
      else print ctxt_print method_text clauses;
    val message = Active.sendback_markup_command (cat_lines lines);
  in
    (state |> tap (fn _ => Output.information message))
  end

fun print_super_isar_skeleton2b ctxt indent keyword stmt i state extra_method_ref extra_method_text  =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
(*
    val state_insert = (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => state )*)
    val ngoals = subgoal_count state
    val state_simp = (case extra_method_ref of (SOME m2) =>  (Seq.the_result "" (Proof.apply m2 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state )
    val nsgoals = subgoal_count state_simp
    val done_or_nil = (if ngoals = 1 then "" else " done")
    val outcome_messages = (if ngoals > nsgoals then [("success", "apply " ^ extra_method_text ^ " (*good, solved without s/h*)")] else 
      Par_List.map (fn (st, txt) => let val p = my_hammer_away 1 st in (fst p, "apply " ^ txt ^ " " ^ Sledgehammer_Commands1.extract_one_liner_proof (snd p)) end) [(state_simp, extra_method_text) (*, (state_insert, m3txt)*)])
    val (retry_outcome, retry_message) = (find_first (fn ("success", _) => true | _ => false) outcome_messages) |> the_default ("failed", "sorry (*failed to find proof*)")
    val (retry_outcome1, retry_message1) = (if retry_outcome = "failed" then (let val sh = my_hammer_away i state in (fst sh, Sledgehammer_Commands1.extract_one_liner_proof (snd sh)) end) else (retry_outcome, retry_message))


    val message1 = (case retry_outcome1 of
        "success" =>   retry_message1 ^ done_or_nil  | 
        _ => "sorry (*failed to find proof*)")

    val inserted_ctxt = ctxt
    val ((inserted_fixes, inserted_assms, inserted_concl), inserted_ctxt') = eigen_context_for_statement stmt inserted_ctxt;
    val if_s = if null inserted_assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term inserted_ctxt' t ) inserted_assms));
    val for_s = if null inserted_fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ inserted_ctxt T) inserted_fixes));

    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;


fun print_super_isar_skeleton2bp ctxt indent keyword stmt i state extra_method_ref extra_method_text  =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
(*
    val state_insert = (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => state )*)
    val ngoals = subgoal_count state
    val state_simp = (case extra_method_ref of (SOME m2) =>  (Seq.the_result "" (Proof.apply m2 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state )
    val nsgoals = subgoal_count state_simp
    val extra_method_text = (if not_needed i then " - " else extra_method_text)
    val done_or_nil = (if ngoals = 1 then "" else " done")
    val outcome_messages = (if ngoals > nsgoals then [("success", "apply " ^ extra_method_text ^ " (*good, solved without s/h*)")] else 
      Par_List.map (fn (st, txt) => let val p = my_hammer_away 1 st in (fst p, "apply " ^ txt ^ " " ^ Sledgehammer_Commands1.extract_one_liner_proof (snd p)) end) [(state_simp, extra_method_text) (*, (state_insert, m3txt)*)])
    val (retry_outcome, retry_message) = (find_first (fn ("success", _) => true | _ => false) outcome_messages) |> the_default ("failed", "sorry (*failed to find proof*)")
    val (retry_outcome1, retry_message1) = (if retry_outcome = "failed" then (let val sh = my_hammer_away i state in (fst sh, Sledgehammer_Commands1.extract_one_liner_proof (snd sh)) end) else (retry_outcome, retry_message))


    val message1 = (case retry_outcome1 of
        "success" =>   retry_message1 ^ done_or_nil  | 
        _ => "sorry (*failed to find proof*)")

    val inserted_ctxt = ctxt
    val ((inserted_fixes, inserted_assms, inserted_concl), inserted_ctxt') = eigen_context_for_statement stmt inserted_ctxt;
    val if_s = if null inserted_assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term inserted_ctxt' t ) inserted_assms));
    val for_s = if null inserted_fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ inserted_ctxt T) inserted_fixes));

    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;


fun hammer_maybe_twice i state =
  let
    val statei = Proof.prefer i state
    val (outcome_type_string, message) = my_hammer_away 1 statei;
    val (retry_outcome, retry_message) = (case outcome_type_string of "success" => (outcome_type_string, message) 
      | _ => my_verbose_hammer_away 1 statei 4)
  in (retry_outcome, retry_message) end;

fun generate_multiple_step_solving_text i state msplit_ref msplit_txt mreduce_ref mreduce_txt = 
  let 
    val state_subgoaled = (#2 o Subgoal.subgoal_cmd Binding.empty_atts NONE (false, [])) (Proof.prefer i state);
    val state_splitted = (case msplit_ref of (SOME m) =>  (Seq.the_result "" (Proof.apply m (state_subgoaled)))
                                         | NONE => state_subgoaled );

    val state_reduced = (case mreduce_ref of (SOME m) =>  (Seq.the_result "" (Proof.apply m (state_splitted)))
                                         | NONE => state_splitted );
    val sub_subgoals_num = (subgoal_count state_reduced);

    val _ = writeln ("sub_subgoals_num: " ^ Int.toString sub_subgoals_num);
    val string_pairs_list = (if sub_subgoals_num > 0 then (Par_List.map (fn j => hammer_maybe_twice j state_reduced) (createList(1, sub_subgoals_num + 1))) else []);
    val proof_text_list = map snd string_pairs_list;
    val proof_text_list = map ( Sledgehammer_Commands1.extract_one_liner_proof) proof_text_list
    val outcome_type_list = map fst string_pairs_list;
    val final_outcome = List.foldl (fn (s, acc) => if s = "success" andalso acc then true else false) true outcome_type_list;
    val done_or_nil = (if sub_subgoals_num = 1 then [] else [" done\n"])
    val text = (if final_outcome then cat_lines (([" apply " ^ msplit_txt ^ " apply " ^ mreduce_txt]) @ proof_text_list @ done_or_nil) else "sorry (*failed to find proof in multi-steps*)\n");
  in text end;
    
    

fun print_super_isar_skeleton3 ctxt indent keyword stmt i state extra_method_ref extra_method_text m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt=
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term ctxt' t ) assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));

    val total_count = subgoal_count state;
    val state_insert = (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state )
    val insert_count = subgoal_count state_insert;
    val (outcome_type_string, message) = (if insert_count < total_count then ("success", "Try this:        (>1.0s)") else hammer_maybe_twice 1 state_insert );
    val done_or_nil = (if insert_count < 2 then "" else "done")
    val message1 = (if outcome_type_string = "success" then "apply " ^ m3txt ^ "(**)" ^  Sledgehammer_Commands1.extract_one_liner_proof message ^ done_or_nil else generate_multiple_step_solving_text i state msplit_ref msplit_txt mreduce_ref mreduce_txt);


    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;


fun print_super_isar_skeleton3p ctxt indent keyword stmt i state extra_method_ref extra_method_text m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt=
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term ctxt' t ) assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));

    val total_count = subgoal_count state;
    val state_insert = (if not_needed i then (case extra_method_ref of (SOME m2) =>  (Seq.the_result "" (Proof.apply m2 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state ) else (case m3ref of (SOME m3) =>  (Seq.the_result "" (Proof.apply m3 (Proof.prefer i state)))
                                         | NONE => Proof.prefer i state ))  
    val insert_count = subgoal_count state_insert;
    val (outcome_type_string, message) = (if insert_count < total_count then ("success", "Try this:        (>1.0s)") else hammer_maybe_twice 1 state_insert);
    val done_or_nil = (if insert_count < 2 then "" else "done")
    val m3txt = (if not_needed i then extra_method_text else m3txt)
    val message1 = (if outcome_type_string = "success" then "apply " ^ m3txt ^ "(**)" ^  Sledgehammer_Commands1.extract_one_liner_proof message ^ done_or_nil else generate_multiple_step_solving_text i state msplit_ref msplit_txt mreduce_ref mreduce_txt);


    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;

fun print_super_isar_skeleton ctxt indent keyword stmt i state  =
  let
    val ((fixes, assms, concl), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
      \<comment> \<open>TODO consider pre-existing indentation -- how?\<close>
    val prefix_sep = "\n" ^ prefix ^ "    and ";
    val show_s = prefix ^ keyword ^ " goal" ^ Int.toString i ^ ": " ^ print_term ctxt' concl;
    val if_s = if null assms then NONE
      else SOME (prefix ^ "  if " ^ space_implode prefix_sep
        (map (fn t => print_term ctxt' t ) assms));
    val for_s = if null fixes then NONE
      else SOME (prefix ^ "  for " ^ space_implode prefix_sep
        (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes));

    val state_i_moved_to_1 = Proof.prefer i state
    val (outcome_type_string, message) = my_hammer_away 1 state_i_moved_to_1;  
    val done_or_nil = (if subgoal_count state < 2 then "" else "done")
    val message1 = (if outcome_type_string = "success" then Sledgehammer_Commands1.extract_one_liner_proof message ^ done_or_nil else "sorry (*failed to find sledgehammer proof*)");


    val s = cat_lines ([show_s] @ map_filter I [if_s, for_s] @
      [ prefix ^  "  " ^ (if is_none if_s then "" else "using that ") ^ message1]);
  in
    s
  end;






fun print_super_sketch2b group_size ctxt method_text1 clauses state method2_ref method_text2  =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton2b ctxt 2 "show" stmt i state method2_ref method_text2) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

fun print_super_sketch2bp group_size ctxt method_text1 clauses state method2_ref method_text2  =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton2bp ctxt 2 "show" stmt i state method2_ref method_text2) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

fun print_super_sketch3 group_size ctxt method_text1 clauses state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton3 ctxt 2 "show" stmt i state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;


fun print_super_sketch3p group_size ctxt method_text1 clauses state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton3p ctxt 2 "show" stmt i state method2_ref method_text2 m3ref m3txt msplit_ref msplit_txt mreduce_ref mreduce_txt) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

fun print_super_sketch group_size ctxt method_text1 clauses state =
  let 
    val n = subgoal_count state;
    val t_start = Timing.start ();
    val s = "proof" ^ method_text1 :: Par_List.map (fn (stmt, i) => print_super_isar_skeleton ctxt 2 "show" stmt i state) (ListPair.zip (clauses, createList'(n))) @ ["qed"]
    val t_end = Timing.result t_start;
  in
    writeln (Timing.message t_end);
    s
  end;

val sketch = print_proof_text_from_state print_sketch;

fun explore method_ref = print_proof_text_from_state print_exploration (SOME method_ref);

fun subgoals options method_ref =
  let
    val apply_line_opt = case method_ref of
        NONE => NONE
      | SOME (_, toks) => SOME ("apply " ^ coalesce_method_txt (map Token.unparse toks))
    val succeed_method_ref = SOME ((Method.succeed_text, Position.no_range), [])
  in
    print_proof_text_from_state (print_subgoals options apply_line_opt) succeed_method_ref
  end;

fun sketch_cmd some_method_text =
  Toplevel.keep_proof (K () o sketch some_method_text o Toplevel.proof_of)

fun explore_cmd method_text =
  Toplevel.keep_proof (K () o explore method_text o Toplevel.proof_of)

fun subgoals_cmd (modes, method_ref) =
  let
    val is_prems = not (member (op =) modes "noprems")
    val is_for = not (member (op =) modes "nofor")
    val is_sh = member (op =) modes "sh"
  in
    Toplevel.keep_proof (K () o subgoals (is_prems, is_for, is_sh) method_ref o Toplevel.proof_of)
  end

fun writeFileln dirname content =
    let val fd = TextIO.openAppend (dirname  ^  ".txt")
        val _ = TextIO.output (fd, String.concat [content, "\n"]) handle e => (TextIO.closeOut fd; raise e)
        val _ = writeln content
        val _ = TextIO.closeOut fd
    in () end;

fun print_proof_text_from_state_generate_oneliners2b print m1 m2  state =
  let
    (*val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state)*)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>

    val method_ref2 = Option.map fst m2
    val method_text2 = case m2 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);




    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'' method_ref2 method_text2);


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    val _ = writeFileln (OS.FileSys.getDir() ^ "/Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str;
  
  in
    (state |> tap (fn _ => Output.information message))
  end

fun nprint_proof_text_from_state_generate_oneliners print m1 state =
  let

  (*  val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state) *)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => " -"
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>




    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'');


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    val _ = writeFileln (OS.FileSys.getDir() ^ "/" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str;
  in
    (state |> tap (fn _ => Output.information message))
  end


fun print_proof_text_from_state_generate_oneliners print m1 state =
  let

  (*  val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state) *)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => " -"
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>




    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'');


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    val _ = writeFileln (OS.FileSys.getDir() ^ "/Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str;
  in
    (state |> tap (fn _ => Output.information message))
  end



fun print_proof_text_from_state_generate_oneliners3 print m1 m2 m3 msplit mreduce state =
  let
    (*val state' = Seq.the_result "" (Proof.proof (Option.map fst m1) state)*)

  
    val state'' = state 
          |> (fn s => (case Option.map fst m1 of SOME m => Seq.the_result "" (Proof.apply m s) | NONE => s))
          
    val { context = ctxt, facts = _, goal } = Proof.goal state'';

    val ctxt_print = fold (fn opt => Config.put opt false)
      [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt

    val method_text1 = case m1 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);
        \<comment> \<open>TODO proper printing required\<close>

    val method_ref2 = Option.map fst m2
    val method_text2 = case m2 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref3 = Option.map fst m3
    val method_text3 = case m3 of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref4 = Option.map fst msplit
    val method_text4 = case msplit of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val method_ref5 = Option.map fst mreduce
    val method_text5 = case mreduce of
        NONE => ""
      | SOME (_, toks) => " " ^ coalesce_method_txt (map Token.unparse toks);

    val goal_props = Logic.strip_imp_prems (Thm.prop_of goal);
    val clauses = map split_clause goal_props;

    val lines = if null clauses then
      if is_none m1 then ["  .."]
      else ["  by" ^ method_text1]
      else (print ctxt_print method_text1 clauses state'' 
        method_ref2 method_text2 
        method_ref3 method_text3 
        method_ref4 method_text4 
        method_ref5 method_text5);


    val lines = lines ;
    val raw_str = cat_lines lines;
    val message = Active.sendback_markup_properties [] (raw_str);
    val _ = writeFileln (OS.FileSys.getDir() ^ "/Results" ^ Context.theory_name {long=false} (Proof_Context.theory_of ctxt) ) raw_str;
  
  in
    (state |> tap (fn _ => Output.information message))
  end


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch\<close>
    "print sketch of Isar proof text after method application"
    (Scan.option (Scan.trace Method.parse) >> sketch_cmd);


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>explore\<close>
    "explore proof obligations after method application as Isar proof text"
    (Scan.trace Method.parse >> explore_cmd);

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch_subgoals\<close>
    "sketch proof obligations as subgoals, applying a method and/or sledgehammer to each"
    (opt_modes -- Scan.option (Scan.trace Method.parse) >> subgoals_cmd);

val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch2b\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) ) >> 
      (fn (meth1_ref, meth2_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners2b (print_super_sketch2b 1) meth1_ref meth2_ref pstate; () end)));

val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch2bp\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) ) >> 
      (fn (meth1_ref, meth2_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners2b (print_super_sketch2bp 1) meth1_ref meth2_ref pstate; () end)));


val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch3\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse)) >> 
      (fn ((((meth1_ref, meth2_ref), meth3_ref), msplit_ref), mreduce_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners3 (print_super_sketch3 1) meth1_ref meth2_ref meth3_ref msplit_ref mreduce_ref pstate; () end)));


val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch3p\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse) -- Scan.option (Scan.trace Method.parse)) >> 
      (fn ((((meth1_ref, meth2_ref), meth3_ref), msplit_ref), mreduce_ref) =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners3 (print_super_sketch3p 1) meth1_ref meth2_ref meth3_ref msplit_ref mreduce_ref pstate; () end)));


val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>super_sketch\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) ) >> 
      (fn meth1_ref =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in print_proof_text_from_state_generate_oneliners (print_super_sketch 1) meth1_ref  pstate; () end)));

val _ = 
  Outer_Syntax.command \<^command_keyword>\<open>nsketch\<close>
    "print sketch of Isar proof text after method application, with oneliners auto generated"
    ((Scan.option (Scan.trace Method.parse) ) >> 
      (fn meth1_ref =>
        Toplevel.keep_proof (fn state => 
          let 
            val pstate = Toplevel.proof_of state;
          in nprint_proof_text_from_state_generate_oneliners (print_numbered_sketch) meth1_ref  pstate; () end)));



\<close>


end
