theory LiveEvictDefs
  imports "Liveness_Top.LiveTop"
begin

text \<open>An Evict at the head of the program of a device that no longer holds the line (a snoop invalidated it
  while the Evict was waiting) has no rule in @{const allTransitions'}, so that device's program stops for
  good. @{text InvalidEvict'} retires the instruction.

  Its rule lemma does not follow from @{const SWMR_state_machine} alone. Three conjuncts constrain a device in
  Invalid whose next instruction is a Store (@{text "C_H_state Invalid nextStore Modified SAD/SA/SD"}), and
  retiring an Evict can bring a Store to the head of the program. For SAD and SD other conjuncts give the
  conclusion; for SA nothing does, and there are states satisfying @{const SWMR_state_machine} (host SA,
  device 0 Invalid with program [Evict, Store], device 1 Modified) in which the step breaks the conjunct.
  Such states are not reachable: @{text SA_inv} below says so, and holds in every reachable state of the
  extended model (LiveEvictTop.thy).\<close>

definition SA_inv :: "Type1State \<Rightarrow> bool" where
  "SA_inv T \<equiv> (HSTATE SA T \<and> CSTATE Invalid T 0 \<longrightarrow> \<not> CSTATE Modified T 1) \<and>
               (HSTATE SA T \<and> CSTATE Invalid T 1 \<longrightarrow> \<not> CSTATE Modified T 0)"

definition "InvalidEvict' T i = (if CSTATE Invalid T i \<and> nextEvict T i then [clearBuffer (T[ -=i i ])] else [])"

definition allTransitions_live2' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where
  "allTransitions_live2' = allTransitions_live' @ [InvalidEvict']"

end
