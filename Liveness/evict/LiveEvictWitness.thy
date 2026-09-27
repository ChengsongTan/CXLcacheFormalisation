theory LiveEvictWitness
  imports LiveEvictTop "Liveness_Witness.LiveWitness"
begin

text \<open>A device whose Shared line is invalidated while an Evict waits at the head of its program. Both
  the original model and the six-rule model of LiveTop.thy stop there; with @{const InvalidEvict'} the
  model continues to a quiescent state. Checked by evaluation.\<close>

definition "step_live2' T = concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_live2')"

lemma step_live2_I: "allTransStar_live2 A T \<Longrightarrow> T' \<in> set (step_live2' T) \<Longrightarrow> allTransStar_live2 A T'"
  unfolding step_live2'_def by (rule allTransStar_live2.step)

definition ev_s0 :: Type1State where "ev_s0 = \<lparr>
    Type1State.hostcache = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.devcache2 = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>,
    Type1State.reqs1 = [], Type1State.reqs2 = [], Type1State.snpresps1 = [], Type1State.snpresps2 = [],
    Type1State.dthdatas1 = [], Type1State.dthdatas2 = [], Type1State.snps1 = [], Type1State.snps2 = [],
    Type1State.reqresps1 = [], Type1State.reqresps2 = [], Type1State.htddatas1 = [], Type1State.htddatas2 = [],
    program1 = [Read 0, Evict], program2 = [Write 1], counter = 0, registers11 = 0, registers12 = 0, registers21 = 0,
    registers22 = 0, clock = 0, buffer1 = None, buffer2 = None \<rparr>"
definition "ev_s1 = hd (InvalidLoad' ev_s0 0)"
definition "ev_s2 = hd (InvalidStore' ev_s1 1)"
definition "ev_s3 = hd (HostInvalidRdShared' ev_s2 0)"
definition "ev_s4 = hd (ISADGO' ev_s3 0)"
definition "ev_s5 = hd (ISDData' ev_s4 0)"
definition "ev_s6 = hd (HostSharedRdOwn' ev_s5 1)"
definition "ev_s7 = hd (SharedSnpInv' ev_s6 0)"
definition "ev_s8 = hd (IMADData' ev_s7 1)"
definition "ev_s9 = hd (HostMARspIHitSE' ev_s8 0)"
definition "ev_s10 = hd (IMAGO' ev_s9 1)"
definition "ev_s11 = hd (InvalidEvict' ev_s10 0)"
lemma ev_trace: "initial_state ev_s0 \<and> InvalidLoad' ev_s0 0 \<noteq> [] \<and> InvalidStore' ev_s1 1 \<noteq> [] \<and> HostInvalidRdShared' ev_s2 0 \<noteq> [] \<and> ISADGO' ev_s3 0 \<noteq> [] \<and> ISDData' ev_s4 0 \<noteq> [] \<and> HostSharedRdOwn' ev_s5 1 \<noteq> [] \<and> SharedSnpInv' ev_s6 0 \<noteq> [] \<and> IMADData' ev_s7 1 \<noteq> [] \<and> HostMARspIHitSE' ev_s8 0 \<noteq> [] \<and> IMAGO' ev_s9 1 \<noteq> []" by eval
lemma ev_stuck: "step' ev_s10 = [] \<and> step_live' ev_s10 = [] \<and> \<not> quiescent ev_s10" by eval
lemma ev_continues: "InvalidEvict' ev_s10 0 \<noteq> [] \<and> quiescent ev_s11" by eval
lemma ev_reachable: "allTransStar_live2 ev_s0 ev_s11"
proof -
  have m: "ev_s1 \<in> set (step_live2' ev_s0) \<and> ev_s2 \<in> set (step_live2' ev_s1) \<and> ev_s3 \<in> set (step_live2' ev_s2) \<and> ev_s4 \<in> set (step_live2' ev_s3) \<and> ev_s5 \<in> set (step_live2' ev_s4) \<and> ev_s6 \<in> set (step_live2' ev_s5) \<and> ev_s7 \<in> set (step_live2' ev_s6) \<and> ev_s8 \<in> set (step_live2' ev_s7) \<and> ev_s9 \<in> set (step_live2' ev_s8) \<and> ev_s10 \<in> set (step_live2' ev_s9) \<and> ev_s11 \<in> set (step_live2' ev_s10)" by eval
  have r0: "allTransStar_live2 ev_s0 ev_s0" by (rule allTransStar_live2.refl)
  have r1: "allTransStar_live2 ev_s0 ev_s1" using step_live2_I[OF r0] m by blast
  have r2: "allTransStar_live2 ev_s0 ev_s2" using step_live2_I[OF r1] m by blast
  have r3: "allTransStar_live2 ev_s0 ev_s3" using step_live2_I[OF r2] m by blast
  have r4: "allTransStar_live2 ev_s0 ev_s4" using step_live2_I[OF r3] m by blast
  have r5: "allTransStar_live2 ev_s0 ev_s5" using step_live2_I[OF r4] m by blast
  have r6: "allTransStar_live2 ev_s0 ev_s6" using step_live2_I[OF r5] m by blast
  have r7: "allTransStar_live2 ev_s0 ev_s7" using step_live2_I[OF r6] m by blast
  have r8: "allTransStar_live2 ev_s0 ev_s8" using step_live2_I[OF r7] m by blast
  have r9: "allTransStar_live2 ev_s0 ev_s9" using step_live2_I[OF r8] m by blast
  have r10: "allTransStar_live2 ev_s0 ev_s10" using step_live2_I[OF r9] m by blast
  have r11: "allTransStar_live2 ev_s0 ev_s11" using step_live2_I[OF r10] m by blast
  then show ?thesis .
qed

end

