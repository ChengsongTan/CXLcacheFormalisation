(*  

Adds "sledgehammer" and related commands to Isabelle/Isar's outer syntax.
author: I tweaked this file to easily call sledgehammer on a proof state, also incuded
utilities for removing comments in generated one-liners.
*)

signature SLEDGEHAMMER_COMMANDS1 =
sig
  type params = Sledgehammer_Prover.params

  val provers : string Unsynchronized.ref
  val default_params : theory -> (string * string) list -> params
  val parse_params: (string * string) list parser
  val my_hammer_away: int -> Proof.state -> (string * string)
  val my_verbose_hammer_away: int -> Proof.state -> int -> (string * string)
  val extract_one_liner_proof: string -> string
end;

structure Sledgehammer_Commands1 : SLEDGEHAMMER_COMMANDS1 =
struct

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


open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay
open Sledgehammer_Isar_Minimize
open Sledgehammer_ATP_Systems
open Sledgehammer_Prover
open Sledgehammer_Prover_ATP
open Sledgehammer_Prover_Minimize
open Sledgehammer_MaSh

val runN = "run"

(** Sledgehammer commands **)

fun add_fact_override ns : fact_override = {add = ns, del = [], only = false}
fun del_fact_override ns : fact_override = {add = [], del = ns, only = false}
fun only_fact_override ns : fact_override = {add = ns, del = [], only = true}
fun merge_fact_override_pairwise (r1 : fact_override) (r2 : fact_override) =
  {add = #add r1 @ #add r2, del = #del r1 @ #del r2, only = #only r1 andalso #only r2}
fun merge_fact_overrides rs = fold merge_fact_override_pairwise rs (only_fact_override [])

(*** parameters ***)

val provers = Unsynchronized.ref ""

type raw_param = string * string list

val default_default_params =
  [("debug", "false"),
   ("verbose", "false"),
   ("overlord", "false"),
   ("spy", "false"),
   ("abduce", "0"),
   ("falsify", "false"),
   ("type_enc", "smart"),
   ("strict", "false"),
   ("lam_trans", "smart"),
   ("uncurried_aliases", "smart"),
   ("learn", "true"),
   ("fact_filter", "smart"),
   ("induction_rules", "smart"),
   ("max_facts", "smart"),
   ("fact_thresholds", "0.45 0.85"),
   ("max_mono_iters", "smart"),
   ("max_new_mono_instances", "smart"),
   ("max_proofs", "1"),
   ("isar_proofs", "smart"),
   ("compress", "smart"),
   ("try0", "false"),
   ("smt_proofs", "true"),
   ("minimize", "false"),
   ("slices", string_of_int (12 * Multithreading.max_threads ())),
   ("preplay_timeout", "1")]

val alias_params =
  [("prover", ("provers", [])), (* undocumented *)
   ("dont_abduce", ("abduce", ["0"])),
   ("dont_preplay", ("preplay_timeout", ["0"])),
   ("dont_compress", ("compress", ["1"])),
   ("dont_slice", ("slices", ["1"])),
   ("isar_proof", ("isar_proofs", [])) (* legacy *)]
val negated_alias_params =
  [("no_debug", "debug"),
   ("quiet", "verbose"),
   ("no_overlord", "overlord"),
   ("dont_spy", "spy"),
   ("dont_falsify", "falsify"),
   ("non_strict", "strict"),
   ("no_uncurried_aliases", "uncurried_aliases"),
   ("dont_learn", "learn"),
   ("no_isar_proofs", "isar_proofs"),
   ("dont_minimize", "minimize"),
   ("dont_try0", "try0"),
   ("no_smt_proofs", "smt_proofs")]

val property_dependent_params = ["provers", "timeout"]

fun is_known_raw_param s =
  AList.defined (op =) default_default_params s orelse
  AList.defined (op =) alias_params s orelse
  AList.defined (op =) negated_alias_params s orelse
  member (op =) property_dependent_params s orelse s = "expect"

fun is_prover_list ctxt s =
  (case space_explode " " s of
    ss as _ :: _ => forall (is_prover_supported ctxt) ss
  | _ => false)

fun unalias_raw_param (name, value) =
  (case AList.lookup (op =) alias_params name of
    SOME (name', []) => (name', value)
  | SOME (param' as (name', _)) =>
    if value <> ["false"] then
      param'
    else
      error ("Parameter " ^ quote name ^ " cannot be set to \"false\" (cf. " ^ quote name' ^ ")")
  | NONE =>
    (case AList.lookup (op =) negated_alias_params name of
      SOME name' => (name',
        (case value of
          ["false"] => ["true"]
        | ["true"] => ["false"]
        | [] => ["false"]
        | _ => value))
    | NONE => (name, value)))

val any_type_enc = type_enc_of_string Strict "erased"

(* "provers =", "type_enc =", "lam_trans =", "fact_filter =", and "max_facts ="
   can be omitted. For the last four, this is a secret feature. *)
fun normalize_raw_param ctxt =
  unalias_raw_param
  #> (fn (name, value) =>
         if is_known_raw_param name then
           (name, value)
         else if null value then
           if is_prover_list ctxt name then
             ("provers", [name])
           else if can (type_enc_of_string Strict) name then
             ("type_enc", [name])
           else if can (trans_lams_of_string ctxt any_type_enc) name then
             ("lam_trans", [name])
           else if member (op =) fact_filters name then
             ("fact_filter", [name])
           else if is_some (Int.fromString name) then
             ("max_facts", [name])
           else
             error ("Unknown parameter: " ^ quote name)
         else
           error ("Unknown parameter: " ^ quote name))

(* Ensures that type encodings such as "mono_native?" and "poly_guards!!" are
   read correctly. *)
val implode_param = strip_spaces_except_between_idents o space_implode " "

(* FIXME: use "Generic_Data" *)
structure Data = Theory_Data
(
  type T = raw_param list
  val empty = default_default_params |> map (apsnd single)
  fun merge data : T = AList.merge (op =) (K true) data
)

(* The first ATP of the list is used by Auto Sledgehammer. *)
fun default_provers_param_value ctxt =
  \<comment> \<open>see also \<^system_option>\<open>sledgehammer_provers\<close>\<close>
  filter (is_prover_installed ctxt) (smts ctxt @ local_atps)
  |> implode_param



fun default_raw_params thy =
  let val ctxt = Proof_Context.init_global thy in
    Data.get thy
    |> fold (AList.default (op =))
       [("provers", [(case !provers of "" => default_provers_param_value ctxt | s => s)]),
        ("timeout",
         let val timeout = Options.default_int \<^system_option>\<open>sledgehammer_timeout\<close> in
           [if timeout <= 0 then "none" else string_of_int timeout]
         end)]
  end

fun extract_params mode default_params override_params =
  let
    val raw_params = rev override_params @ rev default_params
    val lookup = Option.map implode_param o AList.lookup (op =) raw_params
    val lookup_string = the_default "" o lookup

    fun general_lookup_bool option default_value name =
      (case lookup name of
        SOME s => parse_bool_option option name s
      | NONE => default_value)
    val lookup_bool = the o general_lookup_bool false (SOME false)
    fun lookup_time name =
      (case lookup name of
        SOME s => parse_time name s
      | NONE => Time.zeroTime)
    fun lookup_int name =
      (case lookup name of
        NONE => 0
      | SOME s =>
        (case Int.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned an integer value")))
    fun lookup_real name =
      (case lookup name of
        NONE => 0.0
      | SOME s =>
        (case Real.fromString s of
          SOME n => n
        | NONE => error ("Parameter " ^ quote name ^ " must be assigned a real value")))
    fun lookup_real_pair name =
      (case lookup name of
        NONE => (0.0, 0.0)
      | SOME s =>
        (case s |> space_explode " " |> map Real.fromString of
          [SOME r1, SOME r2] => (r1, r2)
        | _ => error ("Parameter " ^ quote name ^ " must be assigned a pair of floating-point \
                 \values (e.g., \"0.6 0.95\")")))
    fun lookup_option lookup' name =
      (case lookup name of
        SOME "smart" => NONE
      | _ => SOME (lookup' name))
    val debug = mode <> Auto_Try andalso lookup_bool "debug"
    val verbose = debug orelse (mode <> Auto_Try andalso lookup_bool "verbose")
    val overlord = lookup_bool "overlord"
    val spy = getenv "SLEDGEHAMMER_SPY" = "yes" orelse lookup_bool "spy"
    val provers = lookup_string "provers" |> space_explode " " |> mode = Auto_Try ? single o hd
    val abduce =
      if mode = Auto_Try then SOME 0
      else lookup_option lookup_int "abduce"
    val falsify =
      if mode = Auto_Try then SOME false
      else lookup_option lookup_bool "falsify"
    val type_enc =
      if mode = Auto_Try then
        NONE
      else
        (case lookup_string "type_enc" of
          "smart" => NONE
        | s => (type_enc_of_string Strict s; SOME s))
    val strict = mode = Auto_Try orelse lookup_bool "strict"
    val lam_trans = lookup_option lookup_string "lam_trans"
    val uncurried_aliases = lookup_option lookup_bool "uncurried_aliases"
    val learn = lookup_bool "learn"
    val fact_filter =
      lookup_option lookup_string "fact_filter"
      |> mode = Auto_Try ? (fn NONE => SOME mepoN | sf => sf)
    val induction_rules =
      lookup_option (the o induction_rules_of_string o lookup_string) "induction_rules"
    val max_facts = lookup_option lookup_int "max_facts"
    val fact_thresholds = lookup_real_pair "fact_thresholds"
    val max_mono_iters = lookup_option lookup_int "max_mono_iters"
    val max_new_mono_instances =
      lookup_option lookup_int "max_new_mono_instances"
    val max_proofs = lookup_int "max_proofs"
    val isar_proofs = lookup_option lookup_bool "isar_proofs"
    val compress = Option.map (curry Real.max 1.0) (lookup_option lookup_real "compress")
    val try0 = lookup_bool "try0"
    val smt_proofs = lookup_bool "smt_proofs"
    val minimize = mode <> Auto_Try andalso lookup_bool "minimize"
    val slices = if mode = Auto_Try then 1 else Int.max (1, lookup_int "slices")
    val timeout = lookup_time "timeout"
    val preplay_timeout = lookup_time "preplay_timeout"
    val expect = lookup_string "expect"
  in
    {debug = debug, verbose = verbose, overlord = overlord, spy = spy, provers = provers,
     abduce = abduce, falsify = falsify, type_enc = type_enc, strict = strict,
     lam_trans = lam_trans, uncurried_aliases = uncurried_aliases, learn = learn,
     fact_filter = fact_filter, induction_rules = induction_rules, max_facts = max_facts,
     fact_thresholds = fact_thresholds, max_mono_iters = max_mono_iters,
     max_new_mono_instances = max_new_mono_instances, max_proofs = max_proofs,
     isar_proofs = isar_proofs, compress = compress, try0 = try0, smt_proofs = smt_proofs,
     minimize = minimize, slices = slices, timeout = timeout, preplay_timeout = preplay_timeout,
     expect = expect}
  end

fun get_params mode = extract_params mode o default_raw_params
fun default_params thy = get_params Normal thy o map (apsnd single)

val silence_state =
  Proof.map_contexts (Try0.silence_methods false #> Config.put SMT_Config.verbose false)

(* Sledgehammer the given subgoal *)


val parse_query_bang = \<^keyword>\<open>?\<close> || \<^keyword>\<open>!\<close> || \<^keyword>\<open>!!\<close>
val parse_key = Scan.repeat1 (Parse.embedded || parse_query_bang) >> implode_param
val parse_value = Scan.repeat1 (Parse.name || Parse.float_number || parse_query_bang)
val parse_param = parse_key -- Scan.optional (\<^keyword>\<open>=\<close> |-- parse_value) []
val parse_raw_params = Scan.optional (Args.bracks (Parse.list parse_param)) []
val parse_params = parse_raw_params >> map (apsnd implode_param)
val parse_fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm)
val parse_fact_override_chunk =
  (Args.add |-- Args.colon |-- parse_fact_refs >> add_fact_override)
  || (Args.add |-- Args.colon |-- Scan.succeed [] >> add_fact_override)
  || (Args.del |-- Args.colon |-- parse_fact_refs >> del_fact_override)
  || (Args.del |-- Args.colon |-- Scan.succeed [] >> del_fact_override)
  || (parse_fact_refs >> only_fact_override)
val parse_fact_override =
  Scan.optional (Args.parens (Scan.repeat parse_fact_override_chunk >> merge_fact_overrides))
    no_fact_override

(*my own sledgehammer *)

type preplay_result = proof_method * (play_outcome * (string * stature) list)

datatype sledgehammer_outcome =
  SH_Some of prover_result * preplay_result list
| SH_Unknown
| SH_TimeOut
| SH_ResourcesOut
| SH_None

fun short_string_of_sledgehammer_outcome (SH_Some _) = "some"
  | short_string_of_sledgehammer_outcome SH_Unknown = "unknown"
  | short_string_of_sledgehammer_outcome SH_TimeOut = "timeout"
  | short_string_of_sledgehammer_outcome SH_ResourcesOut = "resources_out"
  | short_string_of_sledgehammer_outcome SH_None = "none"

fun alternative f (SOME x) (SOME y) = SOME (f (x, y))
  | alternative _ (x as SOME _) NONE = x
  | alternative _ NONE (y as SOME _) = y
  | alternative _ NONE NONE = NONE

fun varify_nonfixed_terms_global nonfixeds tm = tm
  |> Same.commit (Term_Subst.map_aterms_same
    (fn Free (x, T) => if member (op =) nonfixeds x then Var ((x, 0), T) else raise Same.SAME
      | Var (xi, _) => raise TERM (Logic.bad_schematic xi, [tm])
      | _ => raise Same.SAME))

fun max_outcome1 outcomes =
  let
    val some = find_first (fn (SH_Some y, msg) =>  not (String.isSubstring "One-line proof reconstruction failed" msg)  | _ => false) outcomes (*author addition: reconstruction failed proofs not valid as proofs*)
    val timeout = find_first (fn (SH_TimeOut, _) => true | _ => false) outcomes
    val resources_out = find_first (fn (SH_ResourcesOut, _) => true | _ => false) outcomes
    val unknown = find_first (fn (SH_Unknown, _) => true | _ => false) outcomes
    val none = find_first (fn (SH_None, _) => true | _ => false) outcomes
  in
    some
    |> alternative snd unknown
    |> alternative snd timeout
    |> alternative snd resources_out
    |> alternative snd none
    |> the_default (SH_Unknown, "")
  end

fun play_one_line_proofs minimize timeout used_facts state goal i methss =
  (if timeout = Time.zeroTime then
     []
   else
     let
       val ctxt = Proof.context_of state
       val used_facts = filter_out (fn (_, (sc, _)) => sc = Chained) used_facts
       val fact_names = map fst used_facts
       val {facts = chained, ...} = Proof.goal state
       val goal_t = Logic.get_goal (Thm.prop_of goal) i

       fun try_methss ress [] = ress
         | try_methss ress (meths :: methss) =
           let
             fun mk_step meths =
               Prove {
                 qualifiers = [],
                 obtains = [],
                 label = ("", 0),
                 goal = goal_t,
                 subproofs = [],
                 facts = ([], fact_names),
                 proof_methods = meths,
                 comment = ""}
             val ress' =
               preplay_isar_step ctxt chained timeout [] (mk_step meths)
               |> map (fn (meth, play_outcome) =>
                  (case (minimize, play_outcome) of
                    (true, Played time) =>
                    let
                      val (time', used_names') =
                        minimized_isar_step ctxt chained time (mk_step [meth])
                        ||> (facts_of_isar_step #> snd)
                      val used_facts' = filter (member (op =) used_names' o fst) used_facts
                    in
                      (meth, Played time', used_facts')
                    end
                  | _ => (meth, play_outcome, used_facts)))
             val any_succeeded = exists (fn (_, Played _, _) => true | _ => false) ress'
           in
             try_methss (ress' @ ress) (if any_succeeded then [] else methss)
           end
     in
       try_methss [] methss
     end)
  |> map (fn (meth, play_outcome, used_facts) =>
    (meth, (play_outcome, filter_out (fn (_, (sc, _)) => sc = Chained) used_facts)))
  |> sort (play_outcome_ord o apply2 (fn (_, (play_outcome, _)) => play_outcome))

fun select_one_line_proof used_facts preferred_meth preplay_results =
  (case preplay_results of
    (* Select best method if preplay succeeded *)
    (best_meth, (best_outcome as Played _, best_used_facts)) :: _ =>
    (best_used_facts, (best_meth, best_outcome))
    (* Otherwise select preferred method *)
  | _ =>
    (used_facts, (preferred_meth,
       (case AList.lookup (op =) preplay_results preferred_meth of
         SOME (outcome, _) => outcome
       | NONE => Play_Timed_Out Time.zeroTime))))
  |> apfst (filter_out (fn (_, (sc, _)) => sc = Chained))

fun launch_prover (params as {verbose, spy, slices, timeout, ...}) mode learn
    (problem as {state, subgoal, factss, ...} : prover_problem)
    (slice as ((slice_size, abduce, falsify, num_facts, fact_filter), _)) name =
  let
    val ctxt = Proof.context_of state

    val _ = spying spy (fn () => (state, subgoal, name,
      "Launched" ^ (if abduce then " (abduce)" else "") ^ (if falsify then " (falsify)" else "")))

    val _ =
      if verbose then
        writeln (name ^ " with " ^ string_of_int num_facts ^ " " ^ fact_filter ^ " fact" ^
          plural_s num_facts ^ " for " ^ string_of_time (slice_timeout slice_size slices timeout) ^
          (if abduce then " (abduce)" else "") ^ (if falsify then " (falsify)" else "") ^ "...")
      else
        ()

    fun print_used_facts used_facts used_from =
      tag_list 1 used_from
      |> map (fn (j, fact) => fact |> apsnd (K j))
      |> filter_used_facts false used_facts
      |> map (fn ((name, _), j) => name ^ "@" ^ string_of_int j)
      |> commas
      |> prefix ("Facts in " ^ name ^ " " ^ (if falsify then "falsification" else "proof") ^ ": ")
      |> writeln

    fun spying_str_of_res ({outcome = NONE, used_facts, used_from, ...} : prover_result) =
        let
          val num_used_facts = length used_facts

          fun find_indices facts =
            tag_list 1 facts
            |> map (fn (j, fact) => fact |> apsnd (K j))
            |> filter_used_facts false used_facts
            |> distinct (eq_fst (op =))
            |> map (prefix "@" o string_of_int o snd)

          fun filter_info (fact_filter, facts) =
            let
              val indices = find_indices facts
              (* "Int.max" is there for robustness *)
              val unknowns = replicate (Int.max (0, num_used_facts - length indices)) "?"
            in
              (commas (indices @ unknowns), fact_filter)
            end

          val filter_infos =
            map filter_info (("actual", used_from) :: factss)
            |> AList.group (op =)
            |> map (fn (indices, fact_filters) => commas fact_filters ^ ": " ^ indices)
        in
          "Success: Found " ^ (if falsify then "falsification" else "proof") ^ " with " ^
          string_of_int num_used_facts ^ " fact" ^ plural_s num_used_facts ^
          (if num_used_facts = 0 then "" else ": " ^ commas filter_infos)
        end
      | spying_str_of_res {outcome = SOME failure, ...} =
        "Failure: " ^ string_of_atp_failure failure
 in
   get_minimizing_prover ctxt mode learn name params problem slice
   |> verbose ? tap (fn {outcome = NONE, used_facts as _ :: _, used_from, ...} =>
       print_used_facts used_facts used_from
     | _ => ())
   |> spy ? tap (fn res => spying spy (fn () => (state, subgoal, name, spying_str_of_res res)))
 end

fun preplay_prover_result ({minimize, preplay_timeout, ...} : params) state goal subgoal
    (result as {outcome, used_facts, preferred_methss, message, ...} : prover_result) =
  let
    val (output, chosen_preplay_outcome) =
      if outcome = SOME ATP_Proof.TimedOut then
        (SH_TimeOut, select_one_line_proof used_facts (fst preferred_methss) [])
      else if outcome = SOME ATP_Proof.OutOfResources then
        (SH_ResourcesOut, select_one_line_proof used_facts (fst preferred_methss) [])
      else if is_some outcome then
        (SH_None, select_one_line_proof used_facts (fst preferred_methss) [])
      else
        let
          val preplay_results =
            play_one_line_proofs minimize preplay_timeout used_facts state goal subgoal
              (snd preferred_methss)
          val chosen_preplay_outcome =
            select_one_line_proof used_facts (fst preferred_methss) preplay_results
        in
          (SH_Some (result, preplay_results), chosen_preplay_outcome)
        end
    fun output_message () = message (fn () => chosen_preplay_outcome)
  in
    (output, output_message)
  end

fun analyze_prover_result_for_inconsistency (result as {outcome, used_facts, ...} : prover_result) =
  if outcome = SOME ATP_Proof.TimedOut then
    (SH_TimeOut, K "")
  else if outcome = SOME ATP_Proof.OutOfResources then
    (SH_ResourcesOut, K "")
  else if is_some outcome then
    (SH_None, K "")
  else
    (SH_Some (result, []), fn () =>
       (if member (op = o apsnd fst) used_facts sledgehammer_goal_as_fact then
          (case map fst (filter_out (equal sledgehammer_goal_as_fact o fst) used_facts) of
            [] => "The goal is inconsistent"
          | facts => "The goal is falsified by these facts: " ^ commas facts)
        else
          "Derived \"False\" from these facts alone: " ^
          commas (map fst used_facts)))

fun check_expected_outcome ctxt prover_name expect outcome =
  let
    val outcome_code = short_string_of_sledgehammer_outcome outcome
  in
    (* The "expect" argument is deliberately ignored if the prover is missing so that
       "Metis_Examples" can be processed on any machine. *)
    if expect = "" orelse not (is_prover_installed ctxt prover_name) then
      ()
    else
      (case (expect, outcome) of
        ("some", SH_Some _) => ()
      | ("some_preplayed", SH_Some (_, preplay_results)) =>
          if exists (fn (_, (Played _, _)) => true | _ => false) preplay_results then
            ()
          else
            error ("Unexpected outcome: the external prover found a proof but preplay failed")
      | ("unknown", SH_Unknown) => ()
      | ("timeout", SH_TimeOut) => ()
      | ("resources_out", SH_ResourcesOut) => ()
      | ("none", SH_None) => ()
      | _ => error ("Unexpected outcome: " ^ quote outcome_code))
  end

fun launch_prover_and_preplay (params as {debug, timeout, expect, ...}) mode
    has_already_found_something found_something massage_message writeln_result learn
    (problem as {state, subgoal, ...}) (slice as ((_, _, falsify, _, _), _)) prover_name =
  let
    val ctxt = Proof.context_of state
    val hard_timeout = Time.scale 5.0 timeout

    fun flip_problem {comment, state, goal, subgoal, factss = factss, ...} =
      let
        val thy = Proof_Context.theory_of ctxt
        val assms = Assumption.all_assms_of ctxt
        val assm_ts = map Thm.term_of assms
        val subgoal_t = Logic.get_goal (Thm.prop_of goal) subgoal
        val polymorphic_subgoal_t = (Logic.list_implies (assm_ts, subgoal_t))
          |> Logic.varify_global
        val nonfixeds =
          subtract (op =) (fold Term.add_free_names assm_ts []) (Term.add_free_names subgoal_t [])
        val monomorphic_subgoal_t = subgoal_t
          |> varify_nonfixed_terms_global nonfixeds
        val subgoal_thms = map (Skip_Proof.make_thm thy)
          [polymorphic_subgoal_t, monomorphic_subgoal_t]
        val new_facts =
          map (fn thm => (((sledgehammer_goal_as_fact, (Assum, General)), thm))) subgoal_thms
      in
        {comment = comment, state = state, goal = Thm.trivial @{cprop False}, subgoal = 1,
         subgoal_count = 1, factss = map (apsnd (append new_facts)) factss,
         has_already_found_something = has_already_found_something,
         found_something = found_something "a falsification"}
      end

    val problem as {goal, ...} = problem |> falsify ? flip_problem

    fun really_go () =
      launch_prover params mode learn problem slice prover_name
      |> (if falsify then analyze_prover_result_for_inconsistency else
        preplay_prover_result params state goal subgoal)

    fun go () =
      if debug then
        really_go ()
      else
        (really_go ()
         handle
           ERROR msg => (SH_Unknown, fn () => msg ^ "\n")
         | exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else (SH_Unknown, fn () => Runtime.exn_message exn ^ "\n"))

    val (outcome, message) = Timeout.apply hard_timeout go ()
    val () = check_expected_outcome ctxt prover_name expect outcome

    val message = message ()
    val () =
      if mode = Auto_Try then
        ()
      else
        (case outcome of
          SH_Some _ =>
          the_default writeln writeln_result (prover_name ^ ": " ^
            massage_message (if falsify then "falsification" else "proof") message)
        | _ => ())
  in
    (outcome, message)
  end

fun string_of_facts filter facts =
  "Selected " ^ string_of_int (length facts) ^ " " ^ (if filter = "" then "" else filter ^ " ") ^
  "fact" ^ plural_s (length facts) ^ ": " ^ (space_implode " " (map (fst o fst) facts))

fun string_of_factss factss =
  if forall (null o snd) factss then
    "Found no relevant facts"
  else
    cat_lines (map (fn (filter, facts) => string_of_facts filter facts) factss)

val default_slice_schedule =
  (* FUDGE (loosely inspired by Seventeen evaluation) *)
  [cvc4N, zipperpositionN, vampireN, veritN, spassN, zipperpositionN, eN, cvc4N, zipperpositionN,
   cvc4N, eN, zipperpositionN, vampireN, cvc4N, cvc4N, vampireN, cvc4N, iproverN, zipperpositionN,
   spassN, vampireN, zipperpositionN, vampireN, zipperpositionN, z3N, zipperpositionN, vampireN,
   iproverN, spassN, zipperpositionN, vampireN, cvc4N, zipperpositionN, z3N, z3N, cvc4N,
   zipperpositionN]

fun schedule_of_provers provers num_slices =
  let
    val (known_provers, unknown_provers) =
      List.partition (member (op =) default_slice_schedule) provers

    val default_slice_schedule = filter (member (op =) known_provers) default_slice_schedule
    val num_default_slices = length default_slice_schedule

    fun round_robin _ [] = []
      | round_robin 0 _ = []
      | round_robin n (prover :: provers) = prover :: round_robin (n - 1) (provers @ [prover])
  in
    if num_slices <= num_default_slices then
      take num_slices default_slice_schedule
    else
      default_slice_schedule
      @ round_robin (num_slices - num_default_slices) (unknown_provers @ known_provers)
  end

fun prover_slices_of_schedule ctxt goal subgoal factss
    ({abduce, falsify, max_facts, fact_filter, type_enc, lam_trans, uncurried_aliases,
      ...} : params)
    schedule =
  let
    fun triplicate_slices original =
      let
        val shift =
          map (apfst (fn (slice_size, abduce, falsify, num_facts, fact_filter) =>
            (slice_size, abduce, falsify, num_facts,
             if fact_filter = mashN then mepoN
             else if fact_filter = mepoN then meshN
             else mashN)))

        val shifted_once = shift original
        val shifted_twice = shift shifted_once
      in
        original @ shifted_once @ shifted_twice
      end

    fun adjust_extra (ATP_Slice (format0, type_enc0, lam_trans0, uncurried_aliases0,
        extra_extra0)) =
        ATP_Slice (format0, the_default type_enc0 type_enc, the_default lam_trans0 lam_trans,
          the_default uncurried_aliases0 uncurried_aliases, extra_extra0)
      | adjust_extra (extra as SMT_Slice _) = extra

    fun adjust_slice max_slice_size
        ((slice_size0, abduce0, falsify0, num_facts0, fact_filter0), extra) =
      let
        val slice_size = Int.min (max_slice_size, slice_size0)
        val the_subgoal = Logic.get_goal (Thm.prop_of goal) subgoal
        val goal_not_False = not (the_subgoal aconv @{prop False})
        val abduce =
          (case abduce of
            NONE => abduce0 andalso goal_not_False
          | SOME max_candidates => max_candidates > 0)
        val falsify =
          (case falsify of
            NONE => falsify0 andalso goal_not_False
          | SOME falsify => falsify)
          andalso not (Term.is_schematic the_subgoal)
        val fact_filter = fact_filter |> the_default fact_filter0
        val max_facts = max_facts |> the_default num_facts0
        val num_facts = Int.min (max_facts, length (facts_of_filter fact_filter factss))
      in
        ((slice_size, abduce, falsify, num_facts, fact_filter), adjust_extra extra)
      end

    val provers = distinct (op =) schedule
    val prover_slices =
      map (fn prover => (prover,
          (is_none fact_filter ? triplicate_slices) (get_slices ctxt prover)))
        provers

    val max_threads = Multithreading.max_threads ()

    fun translate_schedule _ 0 _ = []
      | translate_schedule _ _ [] = []
      | translate_schedule prover_slices slices_left (prover :: schedule) =
        (case AList.lookup (op =) prover_slices prover of
          SOME (slice0 :: slices) =>
          let
            val prover_slices' = AList.update (op =) (prover, slices) prover_slices
            val slice as ((slice_size, _, _, _, _), _) =
              adjust_slice ((slices_left + max_threads - 1) div max_threads) slice0
          in
            (prover, slice) :: translate_schedule prover_slices' (slices_left - slice_size) schedule
          end
        | _ => translate_schedule prover_slices slices_left schedule)
  in
    translate_schedule prover_slices (length schedule) schedule
    |> distinct (op =)
  end

fun my_run_sledgehammer (params as {verbose, spy, provers, falsify, induction_rules, max_facts,
    max_proofs, slices, ...}) mode writeln_result i (fact_override as {only, ...}) state =
  if null provers then
    error "No prover is set"
  else
    (case subgoal_count state of
      0 => (error "No subgoal!"; (false, (SH_None, "")))
    | n =>
      let
        val _ = Proof.assert_backward state
        val print = if mode = Normal andalso is_none writeln_result then writeln else K ()

        val found_proofs_and_falsifications = Synchronized.var "found_proofs_and_falsifications" 0

        fun has_already_found_something () =
          if mode = Normal then
            Synchronized.value found_proofs_and_falsifications > 0
          else
            false

        fun found_something a_proof_or_inconsistency prover_name =
          if mode = Normal then
            (Synchronized.change found_proofs_and_falsifications (fn n => n + 1);
             (the_default writeln writeln_result) (prover_name ^ " found " ^
             a_proof_or_inconsistency ^ "..."))
          else
            ()

        val seen_messages = Synchronized.var "seen_messages" ([] : string list)

        fun strip_until_left_paren "" = ""
          | strip_until_left_paren s =
            let
              val n = String.size s
              val s' = String.substring (s, 0, n - 1)
            in
              s' |> String.substring (s, n - 1, 1) <> "(" ? strip_until_left_paren
            end

        (* Remove the measured preplay time when looking for duplicates. This is
           admittedly rather ad hoc. *)
        fun strip_time s =
          if String.isSuffix " s)" s orelse String.isSuffix " ms)" s then
            strip_until_left_paren s
          else
            s

        fun massage_message proof_or_inconsistency s =
          let val s' = strip_time s in
            if member (op =) (Synchronized.value seen_messages) s' then
              "Found duplicate " ^ proof_or_inconsistency
            else
              (Synchronized.change seen_messages (cons s'); s)
          end

        val ctxt = Proof.context_of state
        val inst_inducts = induction_rules = SOME Instantiate
        val {facts = chained_thms, goal, ...} = Proof.goal state
        val (_, hyp_ts, concl_t) = strip_subgoal goal i ctxt
        val _ =
          (case find_first (not o is_prover_supported ctxt) provers of
            SOME name => error ("No such prover: " ^ name)
          | NONE => ())
        val _ = print "Sledgehammering..."
        val _ = spying spy (fn () => (state, i, "***", "Starting " ^ str_of_mode mode ^ " mode"))
        val ({elapsed, ...}, all_facts) = Timing.timing
          (nearly_all_facts_of_context ctxt inst_inducts fact_override chained_thms hyp_ts) concl_t
        val _ = spying spy (fn () => (state, i, "All",
          "Extracting " ^ string_of_int (length all_facts) ^ " facts from background theory in " ^
          string_of_int (Time.toMilliseconds elapsed) ^ " ms"))

        val spying_str_of_factss =
          commas o map (fn (filter, facts) => filter ^ ": " ^ string_of_int (length facts))

        fun get_factss provers =
          let
            val max_max_facts =
              (case max_facts of
                SOME n => n
              | NONE =>
                fold (fn prover =>
                      fold (fn ((_, _, _, max_facts, _), _) => Integer.max max_facts)
                    (get_slices ctxt prover))
                  provers 0)
              * 51 div 50  (* some slack to account for filtering of induction facts below *)

            val ({elapsed, ...}, factss) = Timing.timing
              (relevant_facts ctxt params (hd provers) max_max_facts fact_override hyp_ts concl_t)
              all_facts

            val induction_rules = the_default (if only then Include else Exclude) induction_rules
            val factss = map (apsnd (maybe_filter_out_induction_rules induction_rules)) factss

            val () = spying spy (fn () => (state, i, "All",
              "Filtering facts in " ^ string_of_int (Time.toMilliseconds elapsed) ^
              " ms (MaSh algorithm: " ^ str_of_mash_algorithm (the_mash_algorithm ()) ^ ")"));
            val () = if verbose then print (string_of_factss factss) else ()
            val () = spying spy (fn () =>
              (state, i, "All", "Selected facts: " ^ spying_str_of_factss factss))
          in
            factss
          end

        fun launch_provers () =
          let
            val factss = get_factss provers
            val problem =
              {comment = "", state = state, goal = goal, subgoal = i, subgoal_count = n,
               factss = factss, has_already_found_something = has_already_found_something,
               found_something = found_something "a proof"}
            val learn = mash_learn_proof ctxt params (Thm.prop_of goal)
            val launch = launch_prover_and_preplay params mode has_already_found_something
              found_something massage_message writeln_result learn

            val schedule =
              if mode = Auto_Try then provers
              else schedule_of_provers provers slices
            val prover_slices = prover_slices_of_schedule ctxt goal i factss params schedule

            val _ =
              if verbose then
                writeln ("Running " ^ commas (map fst prover_slices) ^ "...")
              else
                ()
          in
            if mode = Auto_Try then
              (SH_Unknown, "")
              |> fold (fn (prover, slice) =>
                  fn accum as (SH_Some _, _) => accum
                    | _ => launch problem slice prover)
                prover_slices
            else
              (learn chained_thms;
               Par_List.map (fn (prover, slice) =>
                   if Synchronized.value found_proofs_and_falsifications < max_proofs then
                     launch problem slice prover
                   else
                     (SH_None, ""))
                 prover_slices
               |> max_outcome1)
          end

        fun normal_failure () =
          (the_default writeln writeln_result
             ("No " ^ (if falsify = SOME true then "falsification" else "proof") ^
              " found");
           false)
      in
        (launch_provers ()
         handle Timeout.TIMEOUT _ => (SH_TimeOut, ""))
        |> `(fn (outcome, message) =>
          (case outcome of
            SH_Some _ => (the_default writeln writeln_result "Done"; true)
          | SH_Unknown =>
            if message = "" then normal_failure ()
            else (the_default writeln writeln_result ("Warning: " ^ message); false)
          | SH_TimeOut => normal_failure ()
          | SH_ResourcesOut => normal_failure ()
          | SH_None =>
            if message = "" then normal_failure ()
            else (the_default writeln writeln_result ("Warning: " ^ message); false)))
      end)







fun my_hammer_away i state0 =
  let
    val state = silence_state state0
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val override_params = [] |> map (normalize_raw_param ctxt)
    val subcommand = runN
  in
    if subcommand = runN then
      let val i = the_default i NONE in
        (my_run_sledgehammer
          (get_params Normal thy override_params) Normal NONE i Sledgehammer_Fact.no_fact_override state) |> (fn (bres, (_, msg)) => if bres then ("success", msg) else ("fail", msg))  
      end
    else
      error ("Unknown subcommand: " ^ quote subcommand)
  end

fun my_verbose_hammer_away i state0 max_proofs_num =
  let
    (* We generally want chained facts to be picked up by the relevance filter, because it can then
       give it a proper name, which is useful for a variety of reasons (minimization, Isar proofs,
       verbose output, machine learning). However, if the fact is available by no other means (not
       even backticks), as "f" would be in "using f unfolding f'" after unfolding, we have no choice
       but to insert it into the state as an additional hypothesis. *)

    val state = silence_state state0

    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state

    val override_params = [("max_proofs", [Int.toString max_proofs_num])] |> map (normalize_raw_param ctxt)

    val subcommand = runN

  in
    if subcommand = runN then
      let val i = the_default i NONE in
         (my_run_sledgehammer
          (get_params Normal thy override_params) Normal NONE i Sledgehammer_Fact.no_fact_override state) |> (fn (bres, (_, msg)) => if bres then ("success", msg) else ("fail", msg))
      end
    else
      error ("Unknown subcommand: " ^ quote subcommand)
  end


fun extract_one_liner_proof input_string =
    let
        (* Define the substring we are looking for *)
        val try_this_prefix = "Try this: "
        val time_start = "(>"
        val time_start2 = "("
        
        (* Function to find the position of a substring *)
        fun find_substring(s, sub) =
            let
                val sub_len = String.size sub
                fun search(i) =
                    if i + sub_len > String.size s then
                        NONE
                    else if String.substring(s, i, sub_len) = sub then
                        SOME i
                    else
                        search(i + 1)
            in
                search(0)
            end

        fun find_last_substring(s, sub) = 
            let 
                val sub_len = String.size sub
                val len = String.size s
                fun search(i) = 
                    if i - sub_len < 0 then
                      NONE
                    else if String.substring(s, i - sub_len, sub_len) = sub then
                      SOME i
                    else 
                      search(i - 1)
            in
              search(len)
            end

        (* Find the starting position of "Try this: " *)
        val start_pos = find_substring(input_string, try_this_prefix)
        
        (* Find the position of "(>" *)
        val time_pos1 = find_substring(input_string, time_start)
        val time_pos = (case time_pos1 of NONE => find_last_substring(input_string, time_start2) | s => s)
    in
        case (start_pos, time_pos) of
            (SOME s, SOME t) =>
                let
                    (* Adjust to get the position after "Try this: " *)
                    val proof_start = s + String.size try_this_prefix
                    (* Adjust to get the position before the time information *)
                    val proof_end = t - 1
                    (* Extract the proof substring *)
                    val proof_string = String.substring(input_string, proof_start, proof_end - proof_start)
                in
                     proof_string
                end
          | _ => "(*  " ^ input_string ^ "  *) sorry"  (* In case the expected patterns are not found *)
    end;

(* Example usage *)
val input_string = "Try this: by (smt (verit) one_le_numeral power2_less_eq_zero_iff power_increasing power_one_right power_zero_numeral) (187 ms)"

val input_string1 = "Try this: by (metis add.commute add_0 add_diff_eq add_increasing2 diff_diff_eq2 diff_ge_0_iff_ge mult.right_neutral mult_1 power2_eq_square right_diff_distrib zero_le_mult_iff zero_le_square) (> 1.0 s, timed out)";
val result = extract_one_liner_proof(input_string);
val _ = writeln result





end;
