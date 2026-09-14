theory CoherenceProperties imports Transposed begin
\<comment>\<open>GTS is defined using a very simplistic approach here, see BugAndRestrictive slide 9 \<close>
definition GTS :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "GTS T i = (if i = 0 then dthdatas2 T = [] \<and> snpresps2 T = [] \<and> snps2 T = [] else dthdatas1 T = [] \<and> snpresps1 T = [] \<and> snps1 T = []) " 


definition nextSnoopPending :: "Type1State  \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "nextSnoopPending T i = (if i = 0 then snps1 T \<noteq> [] else snps2 T \<noteq> [])"

definition nextReqPending :: "Type1State  \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "nextReqPending T i = (if i = 0 then reqs1 T \<noteq> [] else reqs2 T \<noteq> [])"



\<comment>\<open>
\<close>
\<comment> \<open>empty list satisfies all.\<close>
fun Lall :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where [simp]:
  "Lall [] p  = True"
| "Lall [a] p = p a"
| "Lall (a # as) p = (p a \<and> Lall as p)"

\<comment> \<open>all elements must satisfy p, and at least one element in queue (nonempty)\<close>
fun LallNonEmpty :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where [simp]:
  "LallNonEmpty [] p  = False"
| "LallNonEmpty [a] p = p a"
| "LallNonEmpty (a # as) p = (p a \<and> LallNonEmpty as p)"


\<comment>\<open>If there exists elements, then at least one need to satisfy. If no elements, fine\<close>
fun Lexists :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where [simp]:
  "Lexists [] p  = True"
| "Lexists [a] p = (p a)"
| "Lexists (a # as) p = (p a \<or> Lexists as p)"

fun Lexists_nonEmpty :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where [simp]:
  "Lexists_nonEmpty [] p  = False"
| "Lexists_nonEmpty (a # as) p = (p a \<or> Lexists_nonEmpty as p)"

definition CXL_SPG_all :: "Type1State \<Rightarrow>  bool"
  where [simp]: "CXL_SPG_all T  = ( ( let snoopToProcess = getTop ((snps1 T) ) 
          in \<not>(exists_earlier_GO (getTime snoopToProcess) (reqresps1 T)  ) ) \<and> ( let snoopToProcess = getTop ((snps2 T) ) 
          in \<not>(exists_earlier_GO (getTime snoopToProcess) (reqresps2 T)  ) )  )"

definition CXL_SPG :: "Type1State \<Rightarrow> nat \<Rightarrow>  bool"
  where [simp]: "CXL_SPG T i = ( if i = 0 then ( let snoopToProcess = getTop ((snps1 T) ) 
          in \<not>(exists_earlier_GO (getTime snoopToProcess) (reqresps1 T)  ) ) else ( let snoopToProcess = getTop ((snps2 T) ) 
          in \<not>(exists_earlier_GO (getTime snoopToProcess) (reqresps2 T)  ) )  )"

\<comment>\<open>2024.01.22 modification: Use simpler version of SPG rule:
  previously used full version CXL_SPG. This makes the guards of each device-taking-snoop rule much larger and the proof more complicated.
  For instance, our previous version requires us to do more case analysis and prove that 
  (\<not> exists_tailgating_GO t msgList \<and> msgList \<noteq> []) ==> exists_earlier_GO t msgList
  holds to deduce a contradiction in the premises when we are proving certain channel message properties in the 
  inductive invariant. With SPG_simple such complex case analysis are avoided.
  The only impact from using SPG_simple on 
  our system is that device-takingsnoop rules will no longer be fired in certain incoherent configurations,
  whereas in previous version they do.\<close>
definition SPG_simple :: "Type1State \<Rightarrow> nat \<Rightarrow>  bool"
  where [simp]: "SPG_simple T i = ( if i = 0 then (reqresps1 T) = [] else (reqresps2 T) = [])"


definition CXL_SPG_used :: "Type1State \<Rightarrow> nat \<Rightarrow>  bool"
  where [simp]: "CXL_SPG_used T i = SPG_simple T i"

(*clear all buffers for all devices*)
\<comment>\<open>We used to clear the buffer so that when a message was placed on a buffer becomes clear,
but this does not seem necessary at the moment: we just need to check if a message has the same timestamp
definition clearBuffer :: "Type1State \<Rightarrow> Type1State" where [simp]:
  "clearBuffer T = T \<lparr> buffer1 :=  None \<rparr>\<lparr> buffer2 := None \<rparr>"
\<close>
definition clearBuffer :: "Type1State \<Rightarrow> Type1State" where [simp]: 
  "clearBuffer T = T"

definition getSnoops :: "nat \<Rightarrow> Type1State \<Rightarrow> Message list " where [simp]: "getSnoops i T = (if i = 0 then snps1 T else snps2 T)" 

(*IMA means data arrived but not GO. This is considered a valid owner state because 3.2.5.2 says "Sending data for a read request 
implies that data is valid, meaning the device can consume it even if the GO has not yet arrived." 
We treat this as a statement for IVA/D to be viewed as in V state
TODO20231126: MIAD counts as owner because *)
definition Owner :: "MESI_State \<Rightarrow> bool" where [simp]:
  "Owner mesi = ( 
    case mesi of Modified \<Rightarrow> True | Exclusive \<Rightarrow> True | IMD \<Rightarrow> True | IMA \<Rightarrow> True | SMA \<Rightarrow> True | 
    SMD \<Rightarrow> True | MIA \<Rightarrow> True | _ \<Rightarrow> False )"

\<comment>\<open>an owner is also a reader\<close>
definition Reader :: "MESI_State \<Rightarrow> bool" where [simp]:  
  "Reader mesi = ( case mesi of Shared \<Rightarrow> True | ISD \<Rightarrow> True | ISA \<Rightarrow> True | SMAD \<Rightarrow> True | SIA \<Rightarrow> True |_ \<Rightarrow> Owner mesi)"

\<comment>\<open> should SMAD be seen as shared or not? \<close>
definition ReaderOnly :: "MESI_State \<Rightarrow> bool" where [simp]:  
  "ReaderOnly mesi = ( case mesi of Shared \<Rightarrow> True | ISD \<Rightarrow> True | ISA \<Rightarrow> True | SMAD \<Rightarrow> True | _ \<Rightarrow> False )"


\<comment>\<open>2 party version: if device 1 is an owner, then device 2 must not be a reader; and vice versa\<close>
definition  SWMR_aux :: "MESI_State \<Rightarrow> MESI_State \<Rightarrow> bool" where [simp]:
  "SWMR_aux state1 state2 = (( Owner state1 \<longrightarrow> \<not> (Reader state2)  ) \<and> (Owner state2 \<longrightarrow> \<not> (Reader state1)))"

definition getGrantedState :: "Message \<Rightarrow> MESI_State" where [simp]:
  "getGrantedState m = (case m of H2DResp txid reqresptype mstate time \<Rightarrow> mstate | _ \<Rightarrow> Invalid)"

\<comment>\<open>either: (i)At most one writer, or (ii)only readers
definition SWMR :: "Type1State \<Rightarrow> bool" where [simp]: 
  "SWMR T = SWMR_aux (CLEntry.block_state (devcache1 T)) (CLEntry.block_state (devcache2 T))"
\<close> 
definition SWMR :: "Type1State \<Rightarrow> bool" where [simp]: 
  "SWMR T =  (((CLEntry.block_state (devcache1 T)) = Modified \<longrightarrow>  (CLEntry.block_state (devcache2 T)) \<noteq> Shared) \<and>  
    ((CLEntry.block_state (devcache2 T)) = Modified \<longrightarrow>  (CLEntry.block_state (devcache1 T)) \<noteq> Shared) ) "


definition C_msg_P_oppo :: "
(MESI_State) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_msg_P_oppo mesi next_msg P T = ((CSTATE mesi T 0 \<and> next_msg T 0 \<longrightarrow> P T 1 ) \<and> (CSTATE mesi T 1 \<and> next_msg T 1 \<longrightarrow> P T 0))"

definition C_msg_P_same :: "
(MESI_State) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_msg_P_same mesi next_msg P T = ((CSTATE mesi T 0 \<and> next_msg T 0 \<longrightarrow> P T 0 ) \<and> (CSTATE mesi T 1 \<and> next_msg T 1 \<longrightarrow> P T 1))"


definition C_msg_P_host :: "
(MESI_State) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (Type1State \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_msg_P_host mesi next_msg P T = ((CSTATE mesi T 0 \<and> next_msg T 0 \<longrightarrow> P T ) \<and> (CSTATE mesi T 1 \<and> next_msg T 1 \<longrightarrow> P T ))"


definition C_not_C_msg :: "
(MESI_State) \<Rightarrow> MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_not_C_msg mesi1 mesi2 P T = ((CSTATE mesi1 T 0 \<longrightarrow> \<not>(CSTATE mesi2 T 1 \<and> P T 1) ) \<and> (CSTATE mesi1 T 1 \<longrightarrow> \<not>(CSTATE mesi2 T 0 \<and> P T 0)))"


definition H_msg_P_same ::  "
HOST_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "H_msg_P_same XAD next_msg P T = ((HSTATE XAD T  \<and> next_msg T 0 \<longrightarrow> P T 0) \<and> (HSTATE XAD T \<and> next_msg T 1 \<longrightarrow> P T 1))"

definition H_msg_P_oppo ::  "
HOST_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "H_msg_P_oppo XAD next_msg P T = ((HSTATE XAD T  \<and> next_msg T 0 \<longrightarrow> P T 1) \<and> (HSTATE XAD T \<and> next_msg T 1 \<longrightarrow> P T 0))"


definition nextDTHDataPending :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "nextDTHDataPending T devNum = (if devNum = 0 then  ((dthdatas1 T)  \<noteq> [])
                                  else if devNum = 1 then ((dthdatas2 T)  \<noteq> []) else False) "

definition no_duplicate_data :: "Type1State \<Rightarrow> bool" where [simp]:
  "no_duplicate_data T = ( (dthdatas1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) \<and> (htddatas1 T \<noteq> [] \<longrightarrow> dthdatas1 T = []) \<and> 
    (dthdatas2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) \<and> (htddatas2 T \<noteq> [] \<longrightarrow> dthdatas2 T = []))"


definition C_H_state :: "MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> MESI_State \<Rightarrow> HOST_State \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_H_state mesi1 P1 mesi2 hst T = ((CSTATE mesi1 T 0 \<and> P1 T 0 \<and> HSTATE hst T \<longrightarrow> \<not>CSTATE  mesi2 T 1) \<and> ((CSTATE mesi1 T 1 \<and> P1 T 1 \<and> HSTATE hst T \<longrightarrow> \<not>CSTATE  mesi2 T 0)))"

definition C_msg_not :: "ReqType \<Rightarrow> MESI_State \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_msg_not reqt mesi T = ((nextReqIs reqt T 0 \<longrightarrow> \<not>CSTATE mesi T 0) \<and> (nextReqIs reqt T 1 \<longrightarrow> \<not>CSTATE mesi T 1))"

definition C_msg_state :: "ReqType \<Rightarrow> MESI_State \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_msg_state reqt mesi T = ((nextReqIs reqt T 0 \<longrightarrow> CSTATE mesi T 0) \<and> (nextReqIs reqt T 1 \<longrightarrow> CSTATE mesi T 1))"


definition C_state_not :: "MESI_State \<Rightarrow> ReqType \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_state_not mesi reqt T = ((CSTATE mesi T 0 \<longrightarrow> \<not>nextReqIs RdShared T 0) \<and> (CSTATE mesi T 1 \<longrightarrow> \<not>nextReqIs RdShared T 1))"


definition H_C_state_msg_same :: "HOST_State \<Rightarrow> MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "H_C_state_msg_same hstate cstate P T = ((HSTATE hstate T \<and> CSTATE cstate T 0 \<longrightarrow> P T 0) \<and> (HSTATE hstate T \<and> CSTATE cstate T 1 \<longrightarrow> P T 1))"

definition H_C_state_msg_oppo :: "HOST_State \<Rightarrow> MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "H_C_state_msg_oppo hstate cstate P T = ((HSTATE hstate T \<and> CSTATE cstate T 0 \<longrightarrow> P T 1) \<and> (HSTATE hstate T \<and> CSTATE cstate T 1 \<longrightarrow> P T 0))"

definition C_m_h_C :: "MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (HOST_State) \<Rightarrow> MESI_State \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_m_h_C mesi P hmesi mesi2 T = ((CSTATE mesi T 0 \<and> P T 0 \<and> HSTATE hmesi T \<longrightarrow> CSTATE mesi2 T 0) \<and> (CSTATE mesi T 1 \<and> P T 1 \<and> HSTATE hmesi T \<longrightarrow> CSTATE mesi2 T 1))"


definition C_m_h_m :: "MESI_State \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> (HOST_State) \<Rightarrow> (Type1State \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> Type1State \<Rightarrow> bool" where [simp]:
  "C_m_h_m mesi P hmesi P2 T = ((CSTATE mesi T 0 \<and> P T 0 \<and> HSTATE hmesi T \<longrightarrow> P2 T 1) \<and> (CSTATE mesi T 1 \<and> P T 1 \<and> HSTATE hmesi T \<longrightarrow> P2  T 0))"

fun singleton_or_empty :: "'a list \<Rightarrow> bool" where
  "singleton_or_empty []   = True"
| "singleton_or_empty [a]  = True"
| "singleton_or_empty as   = False"

fun singleton_list :: "'a list \<Rightarrow> bool" where
  "singleton_list []   = True"
| "singleton_list [a]  = True"
| "singleton_list as   = False"

definition nextDTHDataFrom :: "nat \<Rightarrow> Type1State \<Rightarrow> bool"
  where [simp]:
  "nextDTHDataFrom devNum T =   ( if devNum = 0 then dthdatas1 T \<noteq> [] else dthdatas2 T \<noteq> [])"

definition nextGOPendingState :: "MESI_State \<Rightarrow> Type1State \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]:
  "nextGOPendingState mesi T devNum = (if devNum = 0 then nextReqRespStateIs mesi (reqresps1 T)  else nextReqRespStateIs mesi (reqresps2 T)  )" 

\<comment>\<open>abandoned sub-predicates: no_duplicate_data T

\<and> 
simpset

    H_msg_P_same SAD nextDTHDataPending  (\<lambda> T i. \<not>(CSTATE Modified T i)) T \<and> 
    H_msg_P_same SD nextDTHDataPending (\<lambda> T i. \<not>(CSTATE Modified T i)) T \<close>
definition SWMR_state_machine :: "Type1State \<Rightarrow> bool" where [simp]:
  "SWMR_state_machine T = ( (SWMR T) \<and>
    C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<and> 
    H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<and> 
    H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<and>
    C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T \<and>
    H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T \<and>
    H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T \<and>
    H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T \<and>
    H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T \<and>
    H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T \<and>
    H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T \<and>
    C_H_state IMAD (nextReqIs RdOwn) Modified SD T \<and>
    C_H_state IMAD (nextReqIs RdOwn) Modified SAD T \<and>
    C_H_state IMAD (nextReqIs RdOwn) Modified SA T \<and>
    C_H_state Invalid nextStore Modified SAD T \<and>
    C_H_state Invalid nextStore Modified SA T \<and>
    C_H_state Invalid nextStore Modified SD T \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) \<and>
    (HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) \<and>
    (HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) \<and>
    C_msg_not RdShared IMAD T \<and>
    C_msg_not RdShared Invalid T \<and>
    H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T \<and>
    C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T \<and>
    C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T \<and>
    C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T \<and>
    C_state_not MIA RdShared T \<and>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T \<and> \<comment>\<open>True because premise false (no GO-WPD should be sent to DE)\<close>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T \<and> \<comment>\<open>True bc premise false\<close>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T \<and> \<comment>\<open>True bc premise false\<close>
    H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T \<and>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T \<and> \<comment>\<open>True and premise might be true\<close>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T \<and>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T \<and>
    H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T \<and>
    C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T \<and>
    C_msg_state RdShared ISAD T \<and>
    C_not_C_msg Modified ISAD nextGOPending T \<and>
    C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T \<and>
    C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T \<and>
    C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T \<and>
    (snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []) \<and>
    (snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []) \<and>
    (length (reqs1 T) \<le> 1 \<and> (length (reqs2 T) \<le> 1)) \<and>
    (length (snps2 T) \<le> 1   \<and> length (snps1 T) \<le> 1) \<and>
    C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T \<and>
    C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T \<and>
    C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T \<and>
    (CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) \<and>
    (CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []) \<and>
    (CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []) \<and>
    (CSTATE Shared T 0 \<longrightarrow> reqs1 T = []) \<and>
    (CSTATE Shared T 1 \<longrightarrow> reqs2 T = []) \<and>
    (CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1) \<and>
    (CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0) \<and>
    (CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T) \<and>
    (CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T) \<and>
    (CSTATE ISD T 0 \<longrightarrow> nextLoad T 0) \<and>
    (CSTATE ISD T 1 \<longrightarrow> nextLoad T 1) \<and>
    (C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T) \<and>
    (length (htddatas1 T) \<le> 1) \<and>
    (length (htddatas2 T) \<le> 1) \<and>
    (CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) \<and>
    (CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) \<and>
    (CSTATE ISD T 0 \<longrightarrow> reqs1 T = []) \<and>
    (CSTATE ISD T 1 \<longrightarrow> reqs2 T = []) \<and>
    (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = []) \<and>
    (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = []) \<and>
    (length (reqresps1 T) \<le> 1) \<and>
    (length (reqresps2 T) \<le> 1) \<and>
    (CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0)  \<longrightarrow> snps1 T = [] ) \<and>
    (CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1)  \<longrightarrow> snps2 T = [] ) \<and>
    (CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) \<and>
    (CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (C_msg_P_same MIA  (nextReqIs DirtyEvict) (nextEvict) T) \<and>
    (reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and>
    (reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) \<and>
    (reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) \<and>
    (HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) \<and>
    (HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) \<and>
    (HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) \<and>
    (HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) \<and>
    (reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = [] ) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = [] ) \<and>
    (HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)) \<and>
    (HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1) \<and>
    (HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) \<and>
    (HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) \<and>
    (length (dthdatas1 T ) \<le> 1) \<and>
    (length (dthdatas2 T ) \<le> 1) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)) \<and>
    (HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1) \<and>
    (HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0) \<and>
    ((nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0) \<and>
    ((nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1) \<and>
    (nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0) \<and>
    (nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or>  CSTATE SIA T 1 \<or> CSTATE IIA T 1) \<and>
    (snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and>
    (snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and>
    (length (snpresps1 T) \<le> 1) \<and>
    (length (snpresps2 T) \<le> 1) \<and>
    (HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 ) \<and>
    (HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 ) \<and>
    (HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []) \<and>
    (HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []) \<and>
    (HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) \<and>
    (HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) \<and>
    (HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) \<and>
    (HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) \<and>
    (HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []) \<and> \<comment>\<open>when host in MD, and 1 device is still sending req, then this req must be from previous owner. In other words, its IWB data must be still inflight according to the semantics of MD\<close>
    (HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []) \<and>
    (HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) \<and> \<comment>\<open>if Data has already been sent for a GO_WritePull, then the device must have already downgraded to Invalid. It might start a new transaction after this, which results in IXAD state\<close>
    (HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) \<and>
    (HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1) \<and> \<comment>\<open>if Data has already been sent for a GO_WritePull, then the device must have already downgraded to Invalid. It might start a new transaction after this, which results in IXAD state\<close>
    (HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0) \<and>
    (dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []) \<and>
    (dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []) \<and>
    (CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0) \<and>
    (CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1) \<and>
    (C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and> \<comment>\<open>True bc premise false\<close>
    (CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) \<and> \<comment>\<open>A weaker invariant for i74:\<not>HSTATE Modified T\<close>
    (CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) \<and>
    (CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0) \<and>
    (CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1) \<and>
    (CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) \<and>
    (CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) \<and>
    ((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) \<and>
    ((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) \<and>
    ((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) \<and>
    ((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) \<and>
    (HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []) \<and> \<comment>\<open> stable state for Host \<longrightarrow> cannot have residue of past transaction on its side\<close>
    (HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) \<and>
    (CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) \<and>
    (CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) \<and>
    (CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1) \<and>
    (CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0) \<and>
    (CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) \<and>
    (CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) \<and>
    (CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) \<and> \<comment>\<open>True, should be narrowed down as some states might not be possible\<close>
    (CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) \<and> \<comment>\<open>symmetric\<close>
    (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1) \<and>
    (CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0) \<and>
    (HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) \<and>
    (CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0) \<and>
    (CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1) \<and>
    (HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) \<and>
    (HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) \<and>
    (nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (nextDTHDataFrom  1 T \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    (nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) \<and>
    (HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1) \<and>
    (HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)) \<and>
    (CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1) \<and>
    (CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0) \<and>
    (CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and>
    (snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    (HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T) \<and>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) \<and>
    (CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) \<and>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) \<and>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T) \<and> \<comment>\<open>True, indeed\<close>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) \<and> \<comment>\<open>True, indeed no new req should happen for SIA\<close>
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and> \<comment>\<open>True, indeed snoop cannot be sent as its downgrading to invalid already known by host\<close>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) \<and> \<comment>\<open>should be narrowed down later\<close>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T) \<and> 
    (C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T) \<and> \<comment>\<open>True, not supposed send any data before GO_WP\<close>
    (CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) \<and> \<comment>\<open>SharedM--> GO inflight already SA--> GO not yet MA\<longrightarrow> other trying to get M\<close>
    (CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) \<and>
    (CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)) \<and>
    (CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)) \<and>
    (C_not_C_msg Modified IMAD nextGOPending T) \<and>
    (CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IMAD T 0 \<longrightarrow> nextStore T 0) \<and>
    (CSTATE IMAD T 1 \<longrightarrow> nextStore T 1) \<and>
    (CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) \<and>
    (CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) \<and>
    (snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and>
    (snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE SMAD T 0 \<longrightarrow> nextStore T 0) \<and>
    (CSTATE SMAD T 1 \<longrightarrow> nextStore T 1) \<and>
    (C_msg_P_same IMA (nextGOPending) nextStore T) \<and>
    (CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    (C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and>
    (C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and>
    (C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) \<and>
    (CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> (  nextHTDDataPending T 0) \<and>  \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0) \<and>
    (CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0)  \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) \<and>
    (CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1)  \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) \<and>
    (CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []) \<and>
    (CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []) \<and>
    (C_msg_P_same SMA (nextGOPending) nextStore T) \<and>
    ((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    ((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) \<and>
    (CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) \<and>
    (CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1) \<and>
    (CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) \<and>
    (CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) \<and>
    ((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)) \<and>
    ((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)) \<and>
    (CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) \<and>
    (CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) \<and>
    (CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) \<and>
    (CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) \<and>
    (CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []) \<and>
    (CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []) \<and>
    (CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T) \<and>
    (CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T) \<and>
    (CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []) \<and>
    (CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = []) \<and>
    (CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) \<and>
    (CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) \<and>
    (CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) \<and>
    (nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1) \<and>
    (CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) \<and>
    (CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1) \<and>
    (CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) \<and>
    (HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) \<and>
    (HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = []) \<and>
    ((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) \<and>
    ((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) \<and>
    (nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0) \<and>
    (nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1) \<and>
    ((CSTATE Invalid T 0  \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) \<and>
    ((CSTATE Invalid T 1  \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) \<and>
    (CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) \<and>
    (CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) \<and>
    (CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) \<and>
    (CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) \<and>
    (CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) \<and>
    (CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) \<and>
    (CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) \<and>
    (CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) \<and>
    (CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) \<and>
    (CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) \<and>
    (CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) \<and>
    (CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) \<and>
    (CSTATE Modified T 0 \<longrightarrow> reqs1 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> reqs2 T = []) \<and>
    (CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0) \<and>
    (nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) \<and>
    (CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) \<and>
    (CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) \<and>
    (CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )) \<and>
    (CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )) \<and>
    (CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) \<and>
    (CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) \<and>
    (HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) \<and>
    (HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1) \<and>
    (C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) \<and>
    (nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)) \<and>
    (nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    (HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) \<and>
    (CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) \<and>
    (nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0) \<and>
    (nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1) \<and>
    (nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1) \<and>
    (nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0) \<and>
    (nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))) \<and>
    (nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T))) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    ((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)) \<and>
    ((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)) \<and>
    ((CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T) \<and>
    (CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    ((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0) \<and>
    ((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1) \<and>
    ((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0) \<and>
    ((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1) \<and>
    ((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    ((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0) \<and>
    (CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and>  \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T) \<and>
    (CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) \<and>
    (CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0) \<and>
    (nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    ((CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) \<and>
    ((CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) \<and>
    (CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) \<and>
    (CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) \<and>
    (CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) \<and>
    (CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0) \<and>
    ((HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1)) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) \<and>
    (HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) \<and>
    (CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) \<and>
    (CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1) \<and>
    (CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    (HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) \<and>
    (HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) \<and>
    (HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    (HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) \<and>
    (CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) \<and>
    (CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) \<and>
    (CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) \<and>
    (CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) \<and>
    (CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) \<and>
    (CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T) \<and>
    (CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T) \<and>
    (CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T) \<and>
    (CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T) \<and>
    (CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    (CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    (CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) \<and>
    (CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0) \<and>
    (CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1) \<and>
    (CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0) \<and>
    (CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) \<and>
    (CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1) \<and>
    (CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []) \<and>
    (CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []) \<and>
    (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []) \<and>
    (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []) \<and>
    (CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) \<and>
    (CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) \<and>
    (CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) \<and>
    (CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) \<and>
    (CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) \<and>
    (CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) \<and>
    (CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) \<and>
    (HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) \<and>
    (HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) \<and>
    (HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0) \<and>
    (HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) \<and>
    (HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) \<and>
    (HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) \<and>
    (HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []) \<and>
    (CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) \<and>
    (CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    (CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    (HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) \<and>
    (HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) \<and>
    (HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) \<and>
    (HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) \<and>
    (CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) \<and>
    (HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) \<and>
    (HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) \<and>
    (HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) \<and>
    (CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) \<and>
    (CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) \<and>
    (CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) \<and>
    (CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) \<and>
    (CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []) \<and>
    (CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1) \<and>
    (HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0) \<and>
    (HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) \<and>
    (CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) \<and>
    (nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) \<and>
    (nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) \<and>
    (HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1) \<and>
    (HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) \<and>
    (HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1) \<and>
    (CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0) \<and>
    (HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) \<and>
    (HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) \<and>
    (HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) \<and>
    (HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1) \<and>
    (HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0) \<and>
    (HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0) \<and>
    (CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)) \<and>
    ((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) \<and>
    ((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0) \<and>
    (CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) \<and>
    (CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) \<and>
    (CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0) \<and>
    (CSTATE Invalid T 0 \<longrightarrow> snps1 T = []) \<and>
    (CSTATE Invalid T 1 \<longrightarrow> snps2 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0) \<and>
    (HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1) \<and>
    (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0) \<and>
    (HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0) \<and>
    (HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1) \<and>
    (HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) \<and>
    (HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) \<and>
    (HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) \<and>
    (length (dthdatas1 T) \<le> 1) \<and>
    (length (dthdatas2 T) \<le> 1) \<and>
    (HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) \<and>
    (CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) \<and>
    (CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) \<and>
    (CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []) \<and>
    (nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) \<and>
    (nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) \<and>
    (CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) \<and>
    (CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) \<and>
    (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []) \<and>
    (HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []) \<and>
    (CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) \<and>
    (CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) \<and>
    (CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) \<and>
    (CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) \<and>
    (CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1) \<and>
    (CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0) \<and>
    (CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []) \<and>
    (HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
    (HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
    (HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) \<and>
    (nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) \<and>
    (nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) \<and>
    (nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T) \<and>
    (nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T) \<and>
    (nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0) \<and>
    (nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1) \<and>
    (CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) \<and>
    (CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) \<and>
    ((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) \<and>
    ((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) \<and>
    ((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) \<and>
    ((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) \<and>
    (HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) \<and>
    (HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) \<and>
    (CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) \<and>
    (CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0)) \<and>
    (HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)  
)"



\<comment>\<open> 
(redundant up till recently) property:
\<and>
    (HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) \<and> \<comment>\<open>potential optimisation: Do not send Data to SMAD\<close>
    (HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1) 

incorrectly added invariants:
    (reqs1 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []  \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []  \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
might be the case that req1 T \<noteq> [] and reqresps1 T \<noteq> []

    C_msg_P_oppo IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not>nextReqPending T i) T : similarly, GO_WritePull+Req might be both pending

    C_msg_P_same Invalid (nextStore) (\<lambda>T i. \<not>nextReqPending T i) T \<and>


old invariant:
    singleton_or_empty (reqs1 T @ snps2 T @ snpresps2 T @...)
lemma singleton_or_empty_fact1: shows "singleton_or_empty (ls1 @ ls2 @ ls3 @ ls4) \<Longrightarrow> singleton_or_empty ls1 \<and> singleton_or_empty ls2 \<and> singleton_or_empty ls3 \<and> singleton_or_empty ls4"  
  by (metis (no_types, lifting) Nil_is_append_conv append.right_neutral append_self_conv2 list.sel(3) singleton_or_empty.elims(2) singleton_or_empty.simps(1) tl_append2)


    old channel invariant
    (reqs1 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (reqs2 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> reqs1 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (snpresps1 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> reqs2 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (dthdatas2 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> reqs1 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) \<and>
    (dthdatas1 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> reqs2 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []) \<and>
    (reqresps1 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqs1 T = []) \<and>
    (reqresps2 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqs2 T = []) \<and>
    (htddatas1 T \<noteq> [] \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqs1 T = []) \<and>
    (htddatas2 T \<noteq> [] \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqs2 T = []) \<and>
    (length (reqs1 T ) \<le> 1) \<and>
    (length (snps2 T ) \<le> 1) \<and>
    (length (snpresps2 T ) \<le> 1) \<and>
    (length (reqresps1 T ) \<le> 1) \<and>
    (length (htddatas1 T ) \<le> 1) \<and>
    (length (reqs2 T ) \<le> 1) \<and>
    (length (snps1 T ) \<le> 1) \<and>
    (length (snpresps1 T ) \<le> 1) \<and>
    (length (reqresps2 T ) \<le> 1) \<and>
    (length (htddatas2 T ) \<le> 1) \<and>


lemma SWMR_singleton_or_empty_reqs1: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (reqs1 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_reqs2: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (reqs2 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_snps1: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (snps1 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_snps2: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (snps2 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_snpresps1: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (snpresps1 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_snpresps2: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (snpresps2 T)"
  using SWMR_state_machine_def singleton_or_empty_fact1 by blast

lemma SWMR_singleton_or_empty_reqresps1: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (reqresps1 T)"



lemma SWMR_singleton_or_empty_reqresps2: shows "SWMR_state_machine T \<Longrightarrow> singleton_or_empty (reqresps2 T)"


lemma SWMR_consume_empty_reqs1: shows "SWMR_state_machine T \<Longrightarrow> (reqs1 (T [ 0 -=req ])) = []"
  apply(subgoal_tac "singleton_or_empty (reqs1 T)")
subgoal 
  using SWMR_singleton_or_empty_reqs1 by blast

lemma SWMR_one_singleton1: shows "\<lbrakk>SWMR_state_machine T; nextSnoopIs X T 0 \<rbrakk> \<Longrightarrow> singleton_list (snps1 T)" 
  by (metis SWMR_singleton_or_empty_snps1 list.distinct(1) list.sel(3) singleton_list.elims(3) singleton_or_empty.elims(2))



\<close>








\<comment>\<open>
M: owner
IMAD+ GO-M : owner
\<close>
  
definition GOwner :: "Type1State \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]: "GOwner T i = (if i = 0 then (Owner (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Owner (getGrantedState m))  )
                       else (Owner (CLEntry.block_state (devcache2 T)) \<or> Lexists_nonEmpty (reqresps2 T) (\<lambda>m. Owner (getGrantedState m))  )) "

definition GReaderOnly :: "Type1State \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]: "GReaderOnly T i = (if i = 0 then (ReaderOnly (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. ReaderOnly (getGrantedState m))  )
                       else (ReaderOnly (CLEntry.block_state (devcache2 T)) \<or> Lexists_nonEmpty (reqresps2 T) (\<lambda>m. ReaderOnly (getGrantedState m))  )) "


definition GReader :: "Type1State \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]: "GReader T i = (if i = 0 then (Reader (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Reader (getGrantedState m))  )
                       else (Reader (CLEntry.block_state (devcache2 T)) \<or> Lexists_nonEmpty (reqresps2 T) (\<lambda>m. Reader (getGrantedState m))  )) "

definition  GSWMR :: "Type1State \<Rightarrow> bool" where [simp]:
  "GSWMR T = (( GOwner T 0  \<longrightarrow> \<not> (GReader T 1)  ) \<and> (GOwner T 1 \<longrightarrow> \<not> (GReader T 0)) )"


\<comment>\<open>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> host_state_configuration_reasonable begins\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> \<close>
definition InvalidFamily :: "MESI_State \<Rightarrow> bool" where [simp]:
  "InvalidFamily mesi = (case mesi of Invalid \<Rightarrow> True | ISAD \<Rightarrow> True | IMAD \<Rightarrow> True | _ \<Rightarrow> False)"

\<comment>\<open>if host believes everyone is Invalid, then indeed all devices don't have any permission\<close>
definition allInvalid :: "Type1State \<Rightarrow> bool" where [simp]: "allInvalid T =   (HSTATE InvalidM T \<longrightarrow> (InvalidFamily (CLEntry.block_state (devcache1 T))  \<and>
  InvalidFamily (CLEntry.block_state (devcache2 T)  )) 
)"

\<comment>\<open>if host believes everyone is in Shared state, then indeed at least one device is in S state, and no device is an owner \<close>
definition allShared :: "Type1State \<Rightarrow> bool" where [simp]: "allShared T =  ( (HSTATE SharedM T 
\<longrightarrow> (((GReader T 0) \<or> (GReader T 1)) \<and> \<not>(GOwner T 0 \<or> GOwner T 1) ) 
))"

\<comment>\<open>if host believes someone is an owner, then there should be exactly one owner\<close>
definition oneModified :: "Type1State \<Rightarrow> bool" where [simp]: "oneModified T =  ( (HSTATE ModifiedM T \<longrightarrow> ( ((GOwner T 0) \<and> \<not>(GOwner T 1)) \<or>
  ((GOwner T 1) \<and> \<not>(GOwner T 0)) )  ) 
)"

definition host_device_states_agree :: "Type1State \<Rightarrow> bool" where [simp]: "host_device_states_agree T = (allInvalid T \<and> allShared T \<and> oneModified T )"

\<comment>\<open>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> host_device_state_agree ends \<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> \<close>







\<comment>\<open>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> host_device_states_reasonable begins\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> \<close>
\<comment>\<open>***********************************************X_means starts****************************************************************************\<close>

definition devStable :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "devStable T i = (let ( reqs) = 
  (if i = 0 then (reqs1 T) else (reqs2 T)) in (reqs = [] \<and> (CSTATE Invalid T i \<or> CSTATE Shared T i \<or> CSTATE Modified T i \<or> CSTATE Exclusive T i ) ))"

definition devJustStarted :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "devJustStarted T i = (let ( reqs) = 
  (if i = 0 then (reqs1 T) else (reqs2 T)) in 
    ((reqs \<noteq> [] \<and> \<not>(CSTATE Invalid T i \<or> CSTATE Shared T i \<or> CSTATE Modified T i \<or> CSTATE Exclusive T i ) ) \<or> (devStable T i)) )"




definition requestorAlmostGotOwnership :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "requestorAlmostGotOwnership T i = ( CSTATE IMAD T i \<and> nextGOPendingState Modified T i \<and> nextHTDDataPending T i
    \<or> CSTATE IMA T i \<and> nextGOPendingState Modified T i \<and> (\<not> nextHTDDataPending T 0) \<or> 
      CSTATE IMD T i \<and> (\<not> nextGOPending T i\<comment>\<open>Not sure what predicate to put here, 
          having a non-Modified GO would still be quite strange state\<close>) \<and> nextHTDDataPending T i)"



definition ownerAlreadyInvalidated :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "ownerAlreadyInvalidated T i = ( CSTATE Invalid T i \<and> \<not>nextSnpRespPending T i \<and> \<not> nextSnoopPending T i \<or> 
    CSTATE IIA T i \<and> nextGOPendingIs GO_WritePull T i \<and> \<not>nextSnpRespPending T i \<and> \<not> nextSnoopPending T i)"

\<comment>\<open>old def of Xmeans: 
(HSTATE ModifiedM T \<or> (HSTATE SharedM T) \<or> (HSTATE InvalidM T) ) \<longrightarrow> 
  ( devJustStarted T 0 \<or> almostCompletion T 0) \<and> ( devJustStarted T 1 \<or> almostCompletion T 1)
Not precise enough and too restrictive\<close>
definition X_means_devStableOrBeginningOrEnding :: "Type1State  \<Rightarrow> bool" where [simp]: "X_means_devStableOrBeginningOrEnding T  = (
  (HSTATE ModifiedM T \<longrightarrow> (requestorAlmostGotOwnership T 0 \<and> ownerAlreadyInvalidated T 1) \<or> (requestorAlmostGotOwnership T 1 \<and> ownerAlreadyInvalidated T 0)  ) 
)"
\<comment>\<open>***********************************************X_means ends****************************************************************************\<close>


\<comment>\<open>***********************************************XD starts********************************************************************************\<close>


definition aboutToGetShared :: "Type1State \<Rightarrow> nat \<Rightarrow> bool"
  where [simp]: "aboutToGetShared T i = (if i = 0 then (CSTATE ISA T 0 \<and> (reqresps1 T) = [] \<or> 
                                                (CSTATE ISAD T 0) \<and> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Shared = (getGrantedState m))  )
                       else (CSTATE ISA T 1 \<and> (reqresps2 T) = [] \<or> 
                                                (CSTATE ISAD T 1) \<and> Lexists_nonEmpty (reqresps2 T) (\<lambda>m. Shared = (getGrantedState m))  ) ) "

definition GONotInflight :: "nat \<Rightarrow> Type1State \<Rightarrow> bool"
  where [simp]: "GONotInflight i T = (if i = 0 then reqresps1 T = [] else reqresps2 T = [])"

definition dthdataInflight :: "Type1State  \<Rightarrow> nat \<Rightarrow> bool" 
   where [simp]: "dthdataInflight T i = (if i = 0 then dthdatas1 T \<noteq> [] else dthdatas2 T \<noteq> [])"

definition dthdataNotInflight :: "Type1State  \<Rightarrow> nat \<Rightarrow> bool" 
   where [simp]: "dthdataNotInflight T i = (if i = 0 then dthdatas1 T = [] else dthdatas2 T = [])"


\<comment>\<open>For instance SD indicates that: the device has responded, with its
SnpResp received by Host, (our transitions will always have the Data and SnpResp sent, and therefore)  
Data still inside D2HData channel (not processed), and the other device is requestor, therefore whould have its state in ISAD (before it got
GO) or ISA (after it got GO)
The Host-device state correspondance can be more refined, for example MD cannot have IMA, but GOwner allows that\<close>
definition  XD_means_devSnoopRespConsumedFirst :: "Type1State  \<Rightarrow> bool" where [simp]: "XD_means_devSnoopRespConsumedFirst T  = (
  ((HSTATE MD T) \<longrightarrow> (nextDTHDataFrom 0 T ) \<and> (GOwner T 1) \<or> (nextDTHDataFrom 1 T ) \<and> (GOwner T 0) ) \<and>
  ((HSTATE SD T) \<longrightarrow> (nextDTHDataFrom 0 T) \<and> (aboutToGetShared T 1) \<or> (nextDTHDataFrom 1 T ) \<and> (aboutToGetShared T 0) ) \<and>
  ((HSTATE ID T) \<longrightarrow> (((nextDTHDataFrom 0 T \<and> GONotInflight 0 T) \<or> 
                          (nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> dthdataNotInflight T 0) \<or> 
                       (nextDTHDataFrom 1 T \<and> GONotInflight 1 T) \<or> 
                          (nextGOPendingIs GO_WritePull T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) \<and> dthdataNotInflight T 1) ) 
)"

\<comment>\<open>***********************************************XD ends********************************************************************************\<close>








\<comment>\<open>***********************************************XA begins********************************************************************************\<close>

definition snprespInflight :: "SnpRespType \<Rightarrow> Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "snprespInflight snpresptype T (i::nat) = (let snpresps = (if i = (0::nat) then (snpresps1 T) else (snpresps2 T)) in
  (Lexists_nonEmpty snpresps (\<lambda>m. snpresptype = (getSpecificTypeSnpResp m))))"


\<comment>\<open>exists number i (the requestor), such that it either is about to get the Data or has already got the Data. But only data is forwarded to it,
go message is not yet ready\<close>
definition onlyDataHasBeenForwardedRdS :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "onlyDataHasBeenForwardedRdS T i = (if i = 0 then (htddatas1 T  \<noteq> [] \<and> CSTATE ISAD T 0  \<or> htddatas1 T = [] \<and> CSTATE ISA T 0 ) 
                                               else (htddatas2 T  \<noteq> [] \<and> CSTATE ISAD T 1  \<or> htddatas2 T = [] \<and> CSTATE ISA T 1 ))"



definition onlyDataHasBeenForwardedRdOwn :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "onlyDataHasBeenForwardedRdOwn T i = (if i = 0 then (htddatas1 T  \<noteq> [] \<and> (CSTATE IMAD T 0 \<or>  CSTATE SMAD T 0)  \<or> 
                                                       htddatas1 T = [] \<and> (CSTATE IMA T 0 \<or>  CSTATE SMA T 0) ) else 
                                                      (htddatas2 T  \<noteq> [] \<and> (CSTATE IMAD T 1  \<or> CSTATE SMAD T 1)  \<or> 
                                                       htddatas2 T = []  \<and> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) ) )"


\<comment>\<open>3.2.4.2.6 RdCurr
These are full cacheline read requests from the device for lines to get the most current data, 
but not change the existing state in any cache, including in the Host. The Host does not need to track the cacheline in the device that 
issued the RdCurr. RdCurr gets a data but no GO.
 The device receives the line in the Invalid state which means it gets one use of the line and cannot cache it\<close>
definition onlyDataHasBeenForwardedRdCurr :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "onlyDataHasBeenForwardedRdCurr T i = (if i = 0 then    (htddatas1 T  \<noteq> []   \<and> CSTATE Invalid T 0 ) else 
                                                      (htddatas2 T \<noteq> [] \<and> CSTATE Invalid T 1 ))"


\<comment>\<open>See table 3-21 on page 103: CXL.cache \u00E2\u0080\u0093 Mapping of H2D Requests to D2H Responses\<close>
definition snpRespNotProcessedData :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "snpRespNotProcessedData T i = ( snprespInflight RspIHitI T i \<and> CSTATE Invalid T i \<or> 
                        snprespInflight RspSFwdM T i \<and> CSTATE Shared T i \<or> snprespInflight RspSHitSE T i \<and> CSTATE Shared T i \<or> 
                        snprespInflight RspIFwdM T i \<and> CSTATE Invalid T i  )"

definition snpRespNotProcessedInv :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "snpRespNotProcessedInv T i = ( snprespInflight RspIHitI T i \<and> CSTATE Invalid T i \<or> 
                         snprespInflight RspIHitSE T i \<and> CSTATE Invalid T i \<or> 
                        snprespInflight RspIFwdM T i \<and> CSTATE Invalid T i  )"


definition snpRespNotProcessedCurr :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "snpRespNotProcessedCurr T i = ( snprespInflight RspIHitI T i \<and> CSTATE Invalid T i \<or> 
                         snprespInflight RspVHitV T i \<and> \<not>(CSTATE Invalid T i) \<or> 
                        snprespInflight RspIFwdM T i \<and> CSTATE Invalid T i \<or> 
                        snprespInflight RspSFwdM T i \<and> CSTATE Shared T i \<or> snprespInflight RspSHitSE T i \<and> CSTATE Shared T i \<or>
                         snprespInflight RspVFwdV T i \<and> \<not>(CSTATE Invalid T i)  )"

\<comment>\<open>Host in MA state, meaning dthdata has been forwarded as htddata, and that might have been received by requestor device. 
 there exists a requestor i, such that i has its data forwarded to it by the host, and the GO response not in-flight (therefore
we know that the SnpResp not processed)
  These  predicates need to be augmented with multiple blocks (say, \<exists>bid msg. msg \<in> htddatas \<and> block_id msg = bid) \<close>
definition XA_means_devDataConsumedFirst :: "Type1State \<Rightarrow> bool" where [simp]:
  "XA_means_devDataConsumedFirst T  = (
  ((HSTATE MA T) \<longrightarrow> ( onlyDataHasBeenForwardedRdOwn T 0 \<and>   (snpRespNotProcessedInv T 1 \<or> nextSnoopPending T 1) \<or> 
                       onlyDataHasBeenForwardedRdOwn T 1 \<and>   (snpRespNotProcessedInv T 0 \<or> nextSnoopPending T 0)  )) 
    \<and>
  ((HSTATE SA T) \<longrightarrow> onlyDataHasBeenForwardedRdS T 0 \<and> (snpRespNotProcessedData T 1 \<or> nextSnoopPending T 1) \<or>
                     onlyDataHasBeenForwardedRdS T 1 \<and> (snpRespNotProcessedData T 0 \<or> nextSnoopPending T 0)  )
 
)
"
\<comment>\<open>***********************************************XA ends********************************************************************************\<close>




\<comment>\<open>***********************************************XAD starts********************************************************************************\<close>


\<comment>\<open>For >1 blocks predicate needs to change to be only about a certain block \<close>
definition snoopInflight :: "SnoopType \<Rightarrow> Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "snoopInflight snptype (T::Type1State) i = 
  (let snoops = (if i = (0::nat) then (snps1 T) else (snps2 T)) in  LallNonEmpty snoops (\<lambda>m. (getSpecificTypeSnoop m = snptype)) 
  ) "


definition  snoopNotInflight :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]:"snoopNotInflight  (T::Type1State) i = 
  (let snoops = (if i = (0::nat) then (snps1 T) else (snps2 T)) in snoops = []  
  ) "



definition snprespNotInflight :: "  Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "snprespNotInflight  T (i::nat) = (let snpresps = (if i = (0::nat) then (snpresps1 T) else (snpresps2 T)) in
  snpresps = [])"
  

\<comment>\<open>If Host is in MAD state, then one is requesting, other is being snooped, and the snoop response and data has not been received by Host yet,
device i we are looking at is the device being snooped
SnpCur does not require transient state changes.
SAD meant some owner has downgraded from M state, therefore RspIHitSE and RspSHitSE might be eliminated \<close>
definition  XAD_means_devBeingSnooped :: " Type1State  \<Rightarrow> bool" where [simp]: "XAD_means_devBeingSnooped T  = 
   ( ( (HSTATE MAD T) \<longrightarrow> ((snoopInflight SnpInv T 0 \<and> dthdataNotInflight T 0 \<and> snprespNotInflight T 0 \<or> 
                            (snoopNotInflight T 0 \<and> dthdataInflight T 0 \<and> snpRespNotProcessedInv T 0 )) \<and> (CSTATE IMAD T 1) \<or>
                           ((snoopInflight SnpInv T 1 \<and> dthdataNotInflight T 1 \<and> snprespNotInflight T 1 \<or> 
                            (snoopNotInflight T 1 \<and> dthdataInflight T 1 \<and> snpRespNotProcessedInv T 1 )) \<and> (CSTATE IMAD T 0) ))) \<and>
     ((HSTATE SAD T) \<longrightarrow> (( (snoopInflight SnpData T 0 \<and> dthdataNotInflight T 0 \<and> snprespNotInflight T 0) \<or> 
                           (snoopNotInflight T 0 \<and> dthdataInflight T 0 \<and> 
                            snpRespNotProcessedData T 0) )   \<and> 
                            (CSTATE ISAD T 1)) \<or> 
                         (( (snoopInflight SnpData T 1 \<and> dthdataNotInflight T 1 \<and> snprespNotInflight T 1) \<or> 
                           (snoopNotInflight T 1 \<and> dthdataInflight T 1 \<and> 
                            snpRespNotProcessedInv T 1) )   \<and> 
                            (CSTATE ISAD T 0))   )   
)"


\<comment>\<open>Note that CSTATE SMAD T i is not possible because there already is an owner\<close>
definition implies_XAD :: " Type1State  \<Rightarrow> bool" where [simp]: "implies_XAD T  = (
 (((CSTATE Modified T 0) \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) \<and>
  ((CSTATE Modified T 1) \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0)) \<and>
 ((CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) \<and>
  (CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0)) \<and>
  ((CSTATE Shared T 0) \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T \<and> ( CSTATE IMAD T 1 \<and> htddatas2 T \<noteq> [] \<or>CSTATE IMA T 1 \<and> htddatas2 T = [] )) \<and>
  ((CSTATE Shared T 1) \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T \<and> ( CSTATE IMAD T 0 \<and> htddatas1 T \<noteq> [] \<or>CSTATE IMA T 0 \<and> htddatas1 T = [] ))
) "
\<comment>\<open>***********************************************XAD ends********************************************************************************\<close>



definition host_state_configuration_reasonable :: "Type1State \<Rightarrow> bool " where [simp]: "host_state_configuration_reasonable T = 
  (X_means_devStableOrBeginningOrEnding T \<and> XD_means_devSnoopRespConsumedFirst T \<and> XA_means_devDataConsumedFirst T \<and> XAD_means_devBeingSnooped T  )"
\<comment>\<open>
definition "reqAlmostComplete T i = ( (HSTATE ModifiedM T  \<or> HSTATE MD T ) \<and> (GOwner T i) \<or> (HSTATE SharedM T  \<or> HSTATE SD T ) \<and> (GReaderOnly T i) )"
\<close>

\<comment>\<open>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> host_state_configuration_reasonable ends \<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds>\<pounds> \<close>




\<comment>\<open>Multiple Snoops to the Same Address
The host is only allowed to have one snoop pending at a time per cacheline address per device. 
The host must wait until it has received both the snoop response and all IWB data (if any) before dispatching the next snoop to that address.


Interpretation (implies) 1: no 2 snoops\<close>
definition no2Snoops :: "Type1State  \<Rightarrow> bool" where [simp]: "no2Snoops T  = 
  ( (length (snps1 T) \<le> 1)  \<and>  
    (length (snps2 T) \<le> 1))"


\<comment>\<open>Interpretation (implies) 2: for same block no 2 snpresps can coexist\<close>
definition no2SnpResps :: "Type1State  \<Rightarrow> bool" where [simp]: "no2SnpResps T  = 
  ( (length (snpresps1 T) \<le> 1)  \<and>  
    (length (snpresps2 T) \<le> 1))"


\<comment>\<open>Interpretation (implies) 3: for same block no snoops and snpresps can coexist\<close>
definition snoopsRespsExclusive :: "Type1State  \<Rightarrow> bool" where [simp]: "snoopsRespsExclusive T  = 
  ( (snps1 T \<noteq> [] \<longrightarrow>  snpresps1 T = []) \<and> (snpresps1 T \<noteq> [] \<longrightarrow> snps1 T = []) \<and>  
    (snps2 T \<noteq> [] \<longrightarrow>  snpresps2 T = []) \<and> ((snpresps2 T \<noteq> [] \<longrightarrow> snps2 T = [])))"


\<comment>\<open>Multiple read requests (cacheable or uncacheable) to the same cacheline are allowed only in the following specific cases 
where [simp]: host tracking state is consistent regardless of the order requests are processed. The host can freely reorder requests, 
so the device is responsible for ordering requests when required. For host memory, multiple RdCurr and/or CLFlush are allowed. 
For these commands the device ends in I-state, so there is no inconsistent state possible for host tracking of a device cache.
No 2 reqs coexist unless they are CLFlush/RdCurr
\<close>
definition no2Reqs :: "Type1State  \<Rightarrow> bool" where [simp]: "no2Reqs T  = 
  ( ((length (reqs1 T) \<le> 1) \<or> Lall (reqs1 T) (\<lambda>req. getSpecificTypeReq req = RdCurr \<or>  getSpecificTypeReq req = CLFlush) \<and>  
    ((length (reqs2 T) \<le> 1) \<or> Lall (reqs1 T) (\<lambda>req. getSpecificTypeReq req = RdCurr \<or>  getSpecificTypeReq req = CLFlush ))))"

\<comment>\<open>Multiple read requests not allowed unless they are CLFlush/RdCurr
resulting invariant 2: at most one reqresp, or all state granted is Invalid
\<close>
definition no2ValidGOs :: "Type1State \<Rightarrow> bool" where [simp]: "no2ValidGOs T = (
  (length (reqresps1 T ) \<le> 1 \<or> Lall (reqresps1 T) (\<lambda>reqresp. getGrantedState reqresp = Invalid)) \<and>
  (length (reqresps2 T ) \<le> 1 \<or> Lall (reqresps2 T) (\<lambda>reqresp. getGrantedState reqresp = Invalid)) )"

definition snpRespCState :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "snpRespCState T i = ((nextSnpRespIs RspIFwdM T i \<longrightarrow> CSTATE Invalid T i) \<and>
  (nextSnpRespIs RspSFwdM T i \<longrightarrow> CSTATE Shared T i) \<and> (nextSnpRespIs RspIHitSE T i \<longrightarrow> CSTATE Invalid T i) \<and> 
  (nextSnpRespIs RspSHitSE T i \<longrightarrow> CSTATE Shared T i)  \<and> (nextSnpRespIs RspVFwdV T i \<longrightarrow> \<not> CSTATE Invalid T i) \<and>
  (nextSnpRespIs RspVHitV T i \<longrightarrow> \<not>CSTATE Invalid T i) \<and>( nextSnpRespIs RspIHitI T i \<longrightarrow> CSTATE Invalid T i ) )"

definition snpRespCorrect :: "Type1State \<Rightarrow> bool" where [simp]: "snpRespCorrect T = (snpRespCState T 0 \<and> 
  snpRespCState T 1 )"


\<comment>\<open>A later-than-t1 issued GO is inside the channel\<close>
fun exists_tailgating_GO :: "nat \<Rightarrow> Message list \<Rightarrow> bool"
  where [simp]: "exists_tailgating_GO t1 (respH # respT) = ((getTime respH > t1 \<and> getSpecificTypeReqResp respH = GO)\<or> exists_tailgating_GO t1 respT)"
  |     "exists_tailgating_GO t1 [] = False"  

\<comment>\<open>returns true if snoop in channel is sent after the GO. When only GO in channel, return false.\<close>
fun snoopBehindGO :: "Message list \<Rightarrow> Message list \<Rightarrow> bool" where [simp]:
  "snoopBehindGO [] glist = True"
| "snoopBehindGO (snoop # slist) glist = ((\<not>exists_tailgating_GO (getTime snoop) glist) \<and> (snoopBehindGO slist glist))"


\<comment>\<open>This is a combined (simplified) snoop-pushes-GO rule and GO-not-tailgating snoops rule: if GO comes first, then GO will
be consumed before that snoop generates a snpresp, and if snoop goes first, that GO should not be sent before
the snpresps generated from snoop has been consumed\<close>

definition snoopGORules :: "Type1State \<Rightarrow> bool" where [simp]: 
  "snoopGORules T = ((snps1 T \<noteq> [] \<longrightarrow> (reqresps1 T = [] \<or> (snoopBehindGO (snps1 T) (reqresps1 T))))  \<and> 
    (snps2 T \<noteq> [] \<longrightarrow> (reqresps2 T = [] \<or> snoopBehindGO (snps2 T) (reqresps2 T))) )"


\<comment>\<open>This is a corallary of the snoop-pushes-GO rule and GO-not-tailgating snoops rule: if GO comes first, then GO will
be consumed before that snoop generates a snpresp, and if snoop goes first, that GO should not be sent before
the snpresps generated from snoop has been consumed\<close>
\<comment>\<open>I thought this would be a corollary, but actually this is not--you can reach this state without violating SPG or GTS,
this is by sending two snoops to two devices simultaneously, and then having  snpresp(dev1) first, (*here violates GTS) generating a GO(dev2) next, 
and then having the
other snpresp(dev2) generated: now both a snpresp and a GO (reqresp) exist for the same device\<close>
\<comment>\<open>HostModifiedSADRspIFwdM' transaction transition not acceptable as sending the GO(dev2) is a tailgate of a snoop(resp)(dev2)\<close>
definition snoopGORules_transitiveP1 :: "Type1State \<Rightarrow> bool" where [simp]: 
  "snoopGORules_transitiveP1 T = ((snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and> (reqresps1 T \<noteq> [] \<longrightarrow> snpresps1 T = []) \<and> 
    (snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"



\<comment>\<open>This is actually the corollary of "no 2 reqs", not used at this stage, might needed in other transition rules\<close>
definition snoopGORules_transitiveP2 :: "Type1State \<Rightarrow> bool" where [simp]:
  "snoopGORules_transitiveP2 T =  ((snpresps1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> (snpresps2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) \<and>
      (snpresps1 T \<noteq> [] \<longrightarrow> snps2 T = []) \<and> (snps2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) \<and> 
      (snpresps2 T \<noteq> [] \<longrightarrow> snps1 T = []) \<and> (snps1 T \<noteq> [] \<longrightarrow> snpresps2 T = []))"
\<comment>\<open>
  "snoopGORules_transitiveP2 T = ((snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) \<and> (reqresps1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) \<and> 
    (snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) \<and> (reqresps2 T \<noteq> [] \<longrightarrow> snpresps1 T = []))"
\<close>

definition no2Datas :: "Type1State \<Rightarrow> bool" where [simp]:
  "no2Datas T = (length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1 \<and> length (htddatas1 T) \<le> 1 \<and> length (htddatas2 T) \<le> 1)"

definition no2DSnoops :: "Type1State \<Rightarrow> bool" where [simp]:
  "no2DSnoops T = ((snps1 T \<noteq> [] \<longrightarrow> snps2 T = []) \<and> (snps2 T \<noteq> [] \<longrightarrow> snps1 T = []))"

definition no2Owners2 :: "Type1State \<Rightarrow> bool" where [simp]:
  "no2Owners2 T = ((CSTATE Modified T 0 \<longrightarrow> reqresps2 T = []) \<and> (CSTATE Modified T 1 \<longrightarrow> reqresps1 T = []) )"

definition transEarlyStageNoGO :: "Type1State \<Rightarrow> bool" where [simp]:
  "transEarlyStageNoGO T = (((CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0) \<longrightarrow> reqresps2 T = []) \<and> 
    ((CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0) \<longrightarrow> reqresps2 T = []) \<and>
    ((CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1) \<longrightarrow> reqresps1 T = []) \<and>
    ((CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1) \<longrightarrow> reqresps1 T = []))"

definition transNoData :: "Type1State \<Rightarrow> bool" where [simp]:
  "transNoData T = (((CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0) \<longrightarrow> htddatas1 T = []) \<and> 
    ((CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1) \<longrightarrow> htddatas2 T = []))"


definition channel_messages_not_redundant :: "Type1State \<Rightarrow> bool" where [simp]: "channel_messages_not_redundant T = 
  (snoopsRespsExclusive T \<and> no2Snoops T \<and> no2SnpResps T \<and> no2Reqs T \<and> snpRespCorrect T \<and> 
    snoopGORules_transitiveP1 T \<and> snoopGORules T \<and> snoopGORules_transitiveP2 T \<and> no2Datas T \<and> no2DSnoops T \<and> 
    no2Owners2 T \<and> transEarlyStageNoGO T \<and> transNoData T) "


definition device_state_reasonable :: "Type1State \<Rightarrow> bool" where [simp]: "device_state_reasonable T = ((CSTATE Invalid T 0 \<longrightarrow> \<not>GOwner T 0) \<and> (CSTATE Invalid T 1 \<longrightarrow> \<not>GOwner T 1) \<and> (CSTATE ISAD T 0 \<longrightarrow> \<not>GOwner T 0) \<and> (CSTATE ISAD T 1 \<longrightarrow> \<not>GOwner T 1) \<and> (CSTATE ISA T 0 \<longrightarrow> \<not>GOwner T 0) \<and> (CSTATE ISA T 1 \<longrightarrow> \<not>GOwner T 1)
  \<and> (CSTATE ISD T 0 \<longrightarrow> \<not>GOwner T 0) \<and> (CSTATE ISD T 1 \<longrightarrow> \<not>GOwner T 1) \<and> (CSTATE Shared T 0 \<longrightarrow> \<not>GOwner T 0) \<and> (CSTATE Shared T 1 \<longrightarrow> \<not>GOwner T 1) )"


\<comment>\<open>For transitions such as IMADData. 
When device is taking data, transaction must have been at the last half, and therefore
either GO has been sent and host is in stable state, or snppresp has not been processed yet and host is in XA state.
But there's one complication: when overall state is in Shared before the transaction, the data could have been sent early.
In that case, there might still be a snoop inflight instead of a snpresp in the H2DReq channel.
 \<and> (nextSnpRespPending T 1 \<or> nextSnoopPending T 1)
\<and> (nextSnpRespPending T 0 \<or> nextSnoopPending T 0)\<close>
definition device_taking_data_states :: "Type1State \<Rightarrow> bool" where [simp]:
  "device_taking_data_states T = 
    ((CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> 
      HSTATE MA T \<or> HSTATE ModifiedM T \<and> nextGOPending T 0) \<and> 
    (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> 
      HSTATE MA T \<or> HSTATE ModifiedM T \<and> nextGOPending T 1))"


definition IMAD_HTDData_overall :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where 
  "IMAD_HTDData_overall T i = (if i = 0 then (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> CSTATE Invalid T 1) else
    ((CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> CSTATE Invalid T 0)))"

definition device_state_configuration_reasonable ::  "Type1State \<Rightarrow> bool" where [simp]:
  "device_state_configuration_reasonable T = ( IMAD_HTDData_overall T 0 \<and> IMAD_HTDData_overall T 1)"


definition state_match_messages :: "Type1State \<Rightarrow> bool " where [simp]:
  "state_match_messages T = ((CSTATE Invalid T 0 \<longrightarrow> htddatas1 T = [] \<and> reqresps1 T = []) \<and> 
    (CSTATE Invalid T 1 \<longrightarrow> htddatas2 T = [] \<and> reqresps2 T = []) \<and> (CSTATE Modified T 0 \<longrightarrow> htddatas1 T = [] \<and> reqresps1 T = []) \<and>
    (CSTATE Modified T 1 \<longrightarrow> htddatas2 T = [] \<and> reqresps2 T = []))"

definition state_messages_hstates :: "Type1State \<Rightarrow> bool " where [simp]:
  "state_messages_hstates T = implies_XAD T"



definition instruction_correct :: "Type1State \<Rightarrow> bool" where [simp]:
  "instruction_correct T = ( (CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0  \<longrightarrow> nextLoad T 0) \<and> 
                             (CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1  \<longrightarrow> nextLoad T 1) \<and> 
                             (CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0  \<longrightarrow> nextStore T 0) \<and>
                             (CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1  \<longrightarrow> nextStore T 1) \<and>
                             (CSTATE MIA T 0 \<or> CSTATE SIA T 0 \<or> CSTATE IIA T 0   \<longrightarrow> nextEvict T 0) \<and>
                             (CSTATE MIA T 1 \<or> CSTATE SIA T 1 \<or> CSTATE IIA T 1   \<longrightarrow> nextEvict T 1) )"



\<comment>\<open>SWMR_inductive, but not necessarily naturally possible. e.g. MD + dthdatas1: [D2HData (Utid 0).., D2HData (Utid 0), ...., D2HData (Utid 1)]
This config will get stuck on this data channel, but we do not care deadlocks (i.e. no next state
exists), we only enforce that  if a next state exists,
then that next state shouldn't be bad.\<close>
definition SWMR_inductive  :: "Type1State \<Rightarrow> bool" where [simp]: 
  "SWMR_inductive T= (host_device_states_agree T \<and> GSWMR T \<and> host_state_configuration_reasonable T \<and> 
                channel_messages_not_redundant T \<and> device_state_reasonable T \<and> device_taking_data_states T \<and> 
                        device_state_configuration_reasonable T \<and> state_match_messages T \<and> state_messages_hstates T \<and> instruction_correct T)"




lemma owner_properties1: shows " CSTATE Invalid T 0
    \<Longrightarrow> Owner (CLEntry.block_state (devcache1 T)) = False"
  unfolding CSTATE_def
  by simp

lemma owner_properties2: shows "\<lbrakk>CSTATE X T 0; X \<noteq> Modified; X \<noteq> Exclusive; X \<noteq> IMA; X \<noteq> IMD;  X \<noteq> MIA; X \<noteq> SMA; X \<noteq> SMD \<rbrakk> \<Longrightarrow> 
  Owner (CLEntry.block_state (devcache1 T)) = False"
  apply(subst Owner_def)
  apply simp
  by (smt (z3) MESI_State.exhaust MESI_State.simps(603) MESI_State.simps(604) MESI_State.simps(605) MESI_State.simps(606) MESI_State.simps(607) MESI_State.simps(608) MESI_State.simps(609) MESI_State.simps(612) MESI_State.simps(613) MESI_State.simps(614) MESI_State.simps(616) MESI_State.simps(617) MESI_State.simps(618) MESI_State.simps(619) MESI_State.simps(622) MESI_State.simps(623) MESI_State.simps(624) MESI_State.simps(625))

lemma nextSnpRespIs_property1: shows "nextSnpRespIs snprespX T 0 \<Longrightarrow> snpresps1 T \<noteq> []"
  unfolding nextSnpRespIs_def
  apply simp
  unfolding startsWithSnpResp_def
  apply(case_tac "snpresps1 T = []")
   apply simp+
  done

lemma nextSnpRespIs_property2: shows "nextSnpRespIs snprespX T 1 \<Longrightarrow> snpresps2 T \<noteq> []"
  unfolding nextSnpRespIs_def
  apply simp
  unfolding startsWithSnpResp_def
  apply(case_tac "snpresps2 T = []")
   apply simp+
  done

lemma CSTATE_GOwner1: shows " \<lbrakk> channel_messages_not_redundant T; CSTATE Invalid T 0; nextSnpRespIs RspIFwdM T 0\<rbrakk> \<Longrightarrow> \<not>GOwner T 0"
  apply(subst GOwner_def)
  unfolding channel_messages_not_redundant_def
  apply(subst simp_thms(6))
  apply(subst if_True)
  apply(subgoal_tac "Owner (CLEntry.block_state (devcache1 T)) = False")
   apply(erule ssubst)
   apply(subst Lattices.disj.left_neutral)
   apply(erule conjE)+
  unfolding snoopGORules_transitiveP1_def
   apply(erule conjE)+
   apply(insert nextSnpRespIs_property1)
  using snoopGORules_transitiveP2_def
  apply (metis Lexists_nonEmpty.simps(1))
  using owner_properties1 by presburger


lemma SnpRespCSTATE: shows " \<lbrakk> channel_messages_not_redundant T; nextSnpRespIs RspIFwdM T 0\<rbrakk> \<Longrightarrow> CSTATE Invalid T 0"
  unfolding channel_messages_not_redundant_def
  apply(erule conjE)+
  unfolding snpRespCState_def snpRespCorrect_def
  apply(erule conjE)+
  by meson
  
 

lemma CSTATE_GOwner2: shows " \<lbrakk> channel_messages_not_redundant T; nextSnpRespIs RspIFwdM T 0\<rbrakk> \<Longrightarrow> \<not>GOwner T 0"
  apply(subst GOwner_def)
  unfolding channel_messages_not_redundant_def
  apply(subst simp_thms(6))
  apply(subst if_True)
  apply(subgoal_tac "Owner (CLEntry.block_state (devcache1 T)) = False")
   apply(erule ssubst)
   apply(subst Lattices.disj.left_neutral)
   apply(erule conjE)+
  unfolding snoopGORules_transitiveP1_def
   apply(erule conjE)+
   apply(insert nextSnpRespIs_property1)
  using snoopGORules_transitiveP2_def 
  apply (metis Lexists_nonEmpty.simps(1))
  apply(subgoal_tac "CSTATE Invalid T 0")
   apply(insert owner_properties2)
  using owner_properties1 apply presburger
  unfolding snpRespCorrect_def
  apply(erule conjE)+
  unfolding snpRespCState_def
  apply(erule conjE)+
  by meson




lemma no2Snoops_invariant_general2: shows "no2Snoops T = no2Snoops ( T  [ j -=snpresp  ] )"
  unfolding no2Snoops_def
  by (simp add: consume_snoopresp_def)

lemma no2Snoops_invariant_general3: shows "no2Snoops T = no2Snoops ( T [ i sHost= X]  )"
  by (simp add: no2Snoops_def)



end