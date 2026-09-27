theory LiveWitness
  imports "Liveness_Top.LiveTop"
begin

text \<open>Executable witnesses for the deadlocks the seven rules remove. Each scenario runs the original model
  from @{const initial_state} into a state in which none of its rules is enabled although requests are
  outstanding, and then continues in the extended model to a quiescent state: both programs retired and
  every channel empty. All checks are by evaluation.\<close>

definition "step' T = concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions')"
definition "step_live' T = concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_live')"
definition "quiescent T = (program1 T = [] \<and> program2 T = [] \<and> reqs1 T = [] \<and> reqs2 T = [] \<and> snps1 T = [] \<and> snps2 T = []
  \<and> reqresps1 T = [] \<and> reqresps2 T = [] \<and> snpresps1 T = [] \<and> snpresps2 T = [] \<and> dthdatas1 T = [] \<and> dthdatas2 T = []
  \<and> htddatas1 T = [] \<and> htddatas2 T = [])"

lemma step_live_I: "allTransStar_live A T \<Longrightarrow> T' \<in> set (step_live' T) \<Longrightarrow> allTransStar_live A T'"
  unfolding step_live'_def by (rule allTransStar_live.step)

subsection \<open>a dirty writeback meets a new read (D1): host I^D\<close>

definition d1_s0 :: Type1State where "d1_s0 = \<lparr>
    Type1State.hostcache = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.devcache2 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.reqs1 = [], Type1State.reqs2 = [], Type1State.snpresps1 = [], Type1State.snpresps2 = [],
    Type1State.dthdatas1 = [], Type1State.dthdatas2 = [], Type1State.snps1 = [], Type1State.snps2 = [],
    Type1State.reqresps1 = [], Type1State.reqresps2 = [], Type1State.htddatas1 = [], Type1State.htddatas2 = [],
    program1 = [Read 0], program2 = [Write 1, Evict], counter = 0, registers11 = 0, registers12 = 0, registers21 = 0,
    registers22 = 0, clock = 0, buffer1 = None, buffer2 = None \<rparr>"
definition "d1_s1 = hd (InvalidLoad' d1_s0 0)"
definition "d1_s2 = hd (InvalidStore' d1_s1 1)"
definition "d1_s3 = hd (HostInvalidRdOwn' d1_s2 1)"
definition "d1_s4 = hd (IMADData' d1_s3 1)"
definition "d1_s5 = hd (IMAGO' d1_s4 1)"
definition "d1_s6 = hd (ModifiedEvict' d1_s5 1)"
definition "d1_s7 = hd (HostModifiedDirtyEvict' d1_s6 1)"
definition "d1_s8 = hd (MIAGO_WritePull' d1_s7 1)"
definition "d1_s9 = hd (HostIDDataLate' d1_s8 1)"
definition "d1_s10 = hd (HostInvalidRdShared' d1_s9 0)"
definition "d1_s11 = hd (ISADGO' d1_s10 0)"
definition "d1_s12 = hd (ISDData' d1_s11 0)"
lemma d1_trace: "initial_state d1_s0 \<and> InvalidLoad' d1_s0 0 \<noteq> [] \<and> InvalidStore' d1_s1 1 \<noteq> [] \<and> HostInvalidRdOwn' d1_s2 1 \<noteq> [] \<and> IMADData' d1_s3 1 \<noteq> [] \<and> IMAGO' d1_s4 1 \<noteq> [] \<and> ModifiedEvict' d1_s5 1 \<noteq> [] \<and> HostModifiedDirtyEvict' d1_s6 1 \<noteq> [] \<and> MIAGO_WritePull' d1_s7 1 \<noteq> []" by eval
lemma d1_stuck: "step' d1_s8 = [] \<and> \<not> quiescent d1_s8" by eval
lemma d1_continues: "HostIDDataLate' d1_s8 1 \<noteq> [] \<and> HostInvalidRdShared' d1_s9 0 \<noteq> [] \<and> ISADGO' d1_s10 0 \<noteq> [] \<and> ISDData' d1_s11 0 \<noteq> [] \<and> quiescent d1_s12" by eval
lemma d1_reachable: "allTransStar_live d1_s0 d1_s12"
proof -
  have m: "d1_s1 \<in> set (step_live' d1_s0) \<and> d1_s2 \<in> set (step_live' d1_s1) \<and> d1_s3 \<in> set (step_live' d1_s2) \<and> d1_s4 \<in> set (step_live' d1_s3) \<and> d1_s5 \<in> set (step_live' d1_s4) \<and> d1_s6 \<in> set (step_live' d1_s5) \<and> d1_s7 \<in> set (step_live' d1_s6) \<and> d1_s8 \<in> set (step_live' d1_s7) \<and> d1_s9 \<in> set (step_live' d1_s8) \<and> d1_s10 \<in> set (step_live' d1_s9) \<and> d1_s11 \<in> set (step_live' d1_s10) \<and> d1_s12 \<in> set (step_live' d1_s11)" by eval
  have r0: "allTransStar_live d1_s0 d1_s0" by (rule allTransStar_live.refl)
  have r1: "allTransStar_live d1_s0 d1_s1" using step_live_I[OF r0] m by blast
  have r2: "allTransStar_live d1_s0 d1_s2" using step_live_I[OF r1] m by blast
  have r3: "allTransStar_live d1_s0 d1_s3" using step_live_I[OF r2] m by blast
  have r4: "allTransStar_live d1_s0 d1_s4" using step_live_I[OF r3] m by blast
  have r5: "allTransStar_live d1_s0 d1_s5" using step_live_I[OF r4] m by blast
  have r6: "allTransStar_live d1_s0 d1_s6" using step_live_I[OF r5] m by blast
  have r7: "allTransStar_live d1_s0 d1_s7" using step_live_I[OF r6] m by blast
  have r8: "allTransStar_live d1_s0 d1_s8" using step_live_I[OF r7] m by blast
  have r9: "allTransStar_live d1_s0 d1_s9" using step_live_I[OF r8] m by blast
  have r10: "allTransStar_live d1_s0 d1_s10" using step_live_I[OF r9] m by blast
  have r11: "allTransStar_live d1_s0 d1_s11" using step_live_I[OF r10] m by blast
  have r12: "allTransStar_live d1_s0 d1_s12" using step_live_I[OF r11] m by blast
  then show ?thesis .
qed

subsection \<open>two RdOwns at a host in S (D3)\<close>

definition d3_s0 :: Type1State where "d3_s0 = \<lparr>
    Type1State.hostcache = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.devcache2 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.reqs1 = [], Type1State.reqs2 = [], Type1State.snpresps1 = [], Type1State.snpresps2 = [],
    Type1State.dthdatas1 = [], Type1State.dthdatas2 = [], Type1State.snps1 = [], Type1State.snps2 = [],
    Type1State.reqresps1 = [], Type1State.reqresps2 = [], Type1State.htddatas1 = [], Type1State.htddatas2 = [],
    program1 = [Write 1], program2 = [Read 0, Write 1], counter = 0, registers11 = 0, registers12 = 0, registers21 = 0,
    registers22 = 0, clock = 0, buffer1 = None, buffer2 = None \<rparr>"
definition "d3_s1 = hd (InvalidLoad' d3_s0 1)"
definition "d3_s2 = hd (InvalidStore' d3_s1 0)"
definition "d3_s3 = hd (HostInvalidRdShared' d3_s2 1)"
definition "d3_s4 = hd (ISADGO' d3_s3 1)"
definition "d3_s5 = hd (ISDData' d3_s4 1)"
definition "d3_s6 = hd (SharedStore' d3_s5 1)"
definition "d3_s7 = hd (HostSharedRdOwnIMAD' d3_s6 1)"
definition "d3_s8 = hd (SMADData' d3_s7 1)"
definition "d3_s9 = hd (SMAGO' d3_s8 1)"
definition "d3_s10 = hd (HostModifiedRdOwn' d3_s9 0)"
definition "d3_s11 = hd (ModifiedSnpInv' d3_s10 1)"
definition "d3_s12 = hd (HostMADData' d3_s11 1)"
definition "d3_s13 = hd (IMADData' d3_s12 0)"
definition "d3_s14 = hd (HostMARspIFwdM' d3_s13 1)"
definition "d3_s15 = hd (IMAGO' d3_s14 0)"
lemma d3_trace: "initial_state d3_s0 \<and> InvalidLoad' d3_s0 1 \<noteq> [] \<and> InvalidStore' d3_s1 0 \<noteq> [] \<and> HostInvalidRdShared' d3_s2 1 \<noteq> [] \<and> ISADGO' d3_s3 1 \<noteq> [] \<and> ISDData' d3_s4 1 \<noteq> [] \<and> SharedStore' d3_s5 1 \<noteq> []" by eval
lemma d3_stuck: "step' d3_s6 = [] \<and> \<not> quiescent d3_s6" by eval
lemma d3_continues: "HostSharedRdOwnIMAD' d3_s6 1 \<noteq> [] \<and> SMADData' d3_s7 1 \<noteq> [] \<and> SMAGO' d3_s8 1 \<noteq> [] \<and> HostModifiedRdOwn' d3_s9 0 \<noteq> [] \<and> ModifiedSnpInv' d3_s10 1 \<noteq> [] \<and> HostMADData' d3_s11 1 \<noteq> [] \<and> IMADData' d3_s12 0 \<noteq> [] \<and> HostMARspIFwdM' d3_s13 1 \<noteq> [] \<and> IMAGO' d3_s14 0 \<noteq> [] \<and> quiescent d3_s15" by eval
lemma d3_reachable: "allTransStar_live d3_s0 d3_s15"
proof -
  have m: "d3_s1 \<in> set (step_live' d3_s0) \<and> d3_s2 \<in> set (step_live' d3_s1) \<and> d3_s3 \<in> set (step_live' d3_s2) \<and> d3_s4 \<in> set (step_live' d3_s3) \<and> d3_s5 \<in> set (step_live' d3_s4) \<and> d3_s6 \<in> set (step_live' d3_s5) \<and> d3_s7 \<in> set (step_live' d3_s6) \<and> d3_s8 \<in> set (step_live' d3_s7) \<and> d3_s9 \<in> set (step_live' d3_s8) \<and> d3_s10 \<in> set (step_live' d3_s9) \<and> d3_s11 \<in> set (step_live' d3_s10) \<and> d3_s12 \<in> set (step_live' d3_s11) \<and> d3_s13 \<in> set (step_live' d3_s12) \<and> d3_s14 \<in> set (step_live' d3_s13) \<and> d3_s15 \<in> set (step_live' d3_s14)" by eval
  have r0: "allTransStar_live d3_s0 d3_s0" by (rule allTransStar_live.refl)
  have r1: "allTransStar_live d3_s0 d3_s1" using step_live_I[OF r0] m by blast
  have r2: "allTransStar_live d3_s0 d3_s2" using step_live_I[OF r1] m by blast
  have r3: "allTransStar_live d3_s0 d3_s3" using step_live_I[OF r2] m by blast
  have r4: "allTransStar_live d3_s0 d3_s4" using step_live_I[OF r3] m by blast
  have r5: "allTransStar_live d3_s0 d3_s5" using step_live_I[OF r4] m by blast
  have r6: "allTransStar_live d3_s0 d3_s6" using step_live_I[OF r5] m by blast
  have r7: "allTransStar_live d3_s0 d3_s7" using step_live_I[OF r6] m by blast
  have r8: "allTransStar_live d3_s0 d3_s8" using step_live_I[OF r7] m by blast
  have r9: "allTransStar_live d3_s0 d3_s9" using step_live_I[OF r8] m by blast
  have r10: "allTransStar_live d3_s0 d3_s10" using step_live_I[OF r9] m by blast
  have r11: "allTransStar_live d3_s0 d3_s11" using step_live_I[OF r10] m by blast
  have r12: "allTransStar_live d3_s0 d3_s12" using step_live_I[OF r11] m by blast
  have r13: "allTransStar_live d3_s0 d3_s13" using step_live_I[OF r12] m by blast
  have r14: "allTransStar_live d3_s0 d3_s14" using step_live_I[OF r13] m by blast
  have r15: "allTransStar_live d3_s0 d3_s15" using step_live_I[OF r14] m by blast
  then show ?thesis .
qed

end
