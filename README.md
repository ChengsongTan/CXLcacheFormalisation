# Artifact Appendix

## A.1 Abstract
This artifact consists of the formal model of the cache coherence protocol of Compute Express Link (CXL)–CXL.cache. It contains the model and proof of the Single-Writer-Multiple-Reader (SWMR) property of CXL.cache in the Isabelle/HOL proof assistant, as described in the paper “Formalising CXL Cache Coherence”. The protocol is modelled as a transition system over system state, where a system state comprises cacheline states, communication channels, buffers and other auxiliary structures.

---

## A.2 Artifact check-list (meta-information)
- **Algorithm**: CXL.cache Cache Coherence Protocol  
- **Program**: Isabelle theories  
- **Compilation**: `isabelle jedit`  
- **Run-time environment**: 
For Windows, double-click the “Cygwin-Terminal.bat” file in the installation folder, and run the command (in the Execution step) from that terminal.  
For Linux/MacOS run from any terminal.
- **Execution**:  
  - First change into the artifact top-level directory.  
  - Then run the command `isabelle jedit -l AllFixes` in the artifact top-level directory.  
- **Output**: Messages shown on the proof state panel indicating theory files have been successfully processed.  
- **How much time is needed to prepare workflow (approximately)?**: 10 minutes  
- **How much time is needed to complete experiments (approximately)?**: 3-10 hours (It is recommended to use a machines with at least 32GB memory to achieve the lower bound.)
- **Publicly available?**: Yes  
- **Workflow automation framework used?**: Isabelle sessions  

---

## A.3 Description
The file that contains the definitions of the system state with type-1 devices (corresponding to the datatype definition in Figure 3 in section 3) is `Transposed.thy` (see line 157 the record definition `Type1State`). Together with the record type, some functions for manipulating certain fields of `Type1State` are also defined. The transition rules as shown in Figure 4 in section 3 of the system are defined in the file `BuggyRules.thy`.

The coherence property that is shown to be an inductive invariant of the system lies in `CoherenceProperties.thy` (see line 199, definition `SWMR_state_machine`).

The `BasicInvariants.thy` file contains some basic invariants related to certain transitions and functions we already defined in `BuggyRules.thy` and `Transposed.thy`.

The proofs are in the rest of the `.thy` files in this artifact. Each transition rule is proven to maintain the inductive property (`SWMR_state_machine`). Since `SWMR_state_machine` is quite large (consisting of 796 conjuncts), the proof of just a single rule is lengthy, each spanning more than 1,000 lines. They are therefore each stored in a dedicated file, where the filename corresponds to the name of the rule (up to a prefix).

As an example, the `FixSIAGO_WritePull.thy` file contains the proof that the `SIAGO_WritePull` rule maintains the `SWMR_state_machine` property. The main lemma stating this fact is at the end of the file (line 3569 with name `SIAGO_WritePull_coherent`).

The most important auxiliary lemma leading to this is `SIAGO_WritePull'_coherent_aux_simpler` (line 149). This auxiliary lemma breaks down the proof into hundreds of subgoals. We call lemmas like this “rule lemmas” as they each correspond to a rule.

The top-level theorem stating the Single-Writer-Multiple-Reader property of the transition system is the corollary `SWMR_pplus_cache` in `TopLevelTheorem.thy` (line 376), corresponding to Theorem 6.2 in the paper. Some main theorems lead to this corollary:
- If `initial_state(𝑇)` then `SWMR_state_machine(𝑇)` (Theorem `initial_valid` in `InitialState.thy`, line 73).  
- If `𝑇 −→ 𝑇’` and `SWMR_state_machine(𝑇)` then `SWMR_state_machine(𝑇’)` (Theorem `all_transitions_coherent_both` at line 337, which combines `all_transitions_coherent` for device index 0 at line 103 and `all_transitions_coherent_dev2` for device index 1 at line 321).  

These two theorems correspond to the first two of the three properties described in the paper just before Theorem 6. Theorem `SWMR_state_machine_CXL_cache` (line 348) combines them: every state reachable from an initial state satisfies `SWMR_state_machine`.

### Changes since the ASPLOS 2025 version of the artifact

* **Model.** Two host rules in `BuggyRules.thy` changed. The conjunct `\<not> (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1)` was removed from the guard of `HostModifiedDirtyEvict'`; it used the fixed device index 1 in both instances of the rule. The guard of `HostMARspIHitSE'` is now `\<not> nextHTDDataPending T i` instead of `htddatas1 T = []`, which tested the H2D data channel of device index 0 in both instances of the rule.
* **Invariant.** Two conjuncts of `SWMR_state_machine` in `CoherenceProperties.thy` were weakened: a device in state `SIA` with a `GO_WritePullDrop` pending may now also coexist with host state `ID`. The rule lemmas (`Fix*.thy`) and `InitialState.thy` were updated accordingly.
* **Both device indices.** The rule lemmas are stated for device index 0. `Toggle.thy` proves that the invariant is symmetric under swapping the two devices (`symmetry`), and `RuleSymmetry.thy` proves that every rule commutes with the swap (`allTransitions'_toggle`). `TopLevelTheorem.thy` combines these into `all_transitions_coherent_both` (line 337), which covers transitions of either device, and `allTransStar` (line 344) is now the reflexive-transitive closure of one-step transitions of either device. The earlier version of `allTransStar` only related a state to its immediate successors under device-0 transitions.
* **Progress assumption of `HostMARspIHitSE'`.** The conjunct `\<not> nextHTDDataPending T i` in the guard of `HostMARspIHitSE'` is not required by CXL; it is a bounded-delay assumption. The theories in `HitSE/` prove that it is redundant, without changing the model or the existing proofs. `HitSE/rules/HitSE_Defs.thy` defines a second invariant `HitSE_inv`: a host in `MA` with a `RspIHitSE` from device i pending has no H2D data pending to i, and a device in `ISD` has no `SnpInv` pending. Each `HitSE/rules/HitSE_<Rule>.thy` shows that the rule preserves `HitSE_inv` in states satisfying `SWMR_state_machine`. `HitSE/top/HitSE_Reach.thy` proves that `HitSE_inv` holds in every reachable state (`HitSE_inv_CXL_cache`); in particular `ISDSnpInv'` never fires (`ISDSnpInv_disabled`). `HitSE/top/GuardFree.thy` defines the model without the conjunct and proves that it reaches exactly the same states (`allTransStar_ng_iff`), so it satisfies `SWMR_pp` as well (`SWMR_pplus_cache_ng`). Build with `isabelle build -d . HitSE_Top`.
* **Session.** `AllFixes` (see `ROOT`) now also contains `InitialState`, `Toggle`, `RuleSymmetry` and `TopLevelTheorem`, so `isabelle build -v -d . AllFixes` checks every theory on which the top-level theorems depend. `Litmus.thy` (scenario tests) and `Super2023.thy` (proof automation) are not part of the session. The artifact was checked with Isabelle2024.

### A.3.1 How to access
The artifact is available on GitHub:  
<https://github.com/ChengsongTan/CXLcacheFormalisation>

### A.3.2 Software dependencies
The artifact depends on Isabelle2024, available at:  
<https://isabelle.in.tum.de/website-Isabelle2024/index.html>

---


---

## Running Experiment

### Preparing suitable running environment
#### For Windows:
Download Isabelle2024 (see above URL). Double-click the downloaded installer to complete the installation process; it is suggested to put Isabelle2024 in some easy-to-access folder such as the desktop so it is easy to navigate there (needed later).
##### Potential issues with downloading and installing Isabelle2024 on Windows
Tested on Windows Server 2022 (Desktop Experience)

(a) If you use Edge and you're not given permission to open the file (e.g. Edge says `Isabelle2024.exe isn't commonly downloaded ...`), do the following:

Click three dots (more actions) > Keep > Show more > Keep anyway. Confirm that we can now execute Isabelle2024.exe.

(b) If Isabelle shows `IO error … (access is denied)`, ignore it & just close Isabelle.

Clone or download the artifact from GitHub (see above URL). If you downloaded a zip of the artifact, uncompress this zip file.

#### For Linux: 
Download using this address:
```
https://isabelle.in.tum.de/website-Isabelle2024/dist/Isabelle2024_linux.tar.gz
```

Then run the command from the command line in the folder where the downloaded file is stored:
```
tar -xzf Isabelle2024_linux.tar.gz
```


To be able to execute the `isabelle` command in the artifact folder, run these commands to add the path to your Isabelle bin directory to your PATH variable:
```
echo 'export PATH=$PATH:/home/ubuntu/Downloads/Isabelle2024/bin' >> ~/.bashrc
```


To make this immediately effective, run:
```
source ~/.bashrc
```


Now try running `isabelle` in the command line, and you should get output like:
```
Usage: isabelle TOOL [ARGS ...]
```

### Download artifact
Download our formalization from the GitHub repository (uncompress if you downloaded the zip file):
```
https://github.com/ChengsongTan/CXLcacheFormalisation
```







### artifact_directory
In the following, `artifact_directory` refers to the artifact’s top-level path. To check that `artifact_directory` is the required folder, confirm that it contains many Isabelle theory files, such as `BasicInvariants.thy`, as well as a file called `ROOT`.
They are in different formats for different operating systems.
Store  `artifact_directory` for later steps. It will have a different format for different operating systems:

#### For Linux/MacOS
In normal Unix-style formats. e.g. `/Users/Joe/CXLcacheFormalisation-main`

#### For Windows
In Cygwin path format. In this format:  
- A Windows path such as:  
```
C:\Users\Joe\CXLcacheFormalisation-main
```

is expressed as:  
```
/cygdrive/c/Users/Joe/CXLcacheFormalisation-main
```
(i.e., replace `C:\` with `/cygdrive/c/` and use forward slashes for the rest of the path).



### Prepare the necessary settings

#### Linux/MacOS
In a terminal, run the command:
```
isabelle getenv ISABELLE_HOME_USER
```
This will output the path of a directory, e.g.,  
```
/home/ubuntu/.isabelle/Isabelle2024
```

#### For Windows
In the Windows explorer, go to the folder where Isabelle2024
is installed and double-click the "Cygwin-Terminal.bat" file
to open a Cygwin terminal (a minimal installation of Cygwin
ships with Isabelle).
In the Cygwin terminal, run `isabelle getenv ISABELLE_HOME_USER`. This will lead to the path of a directory being output, e.g.
```
/cygdrive/c/Users/Joe/.isabelle/Isabelle2024
```
Navigate to the directory. If you use Windows Explorer and the path is `cygdrive/c/...`, this means `c/...` "


### Run the workflow: preparation
After navigating to the directory as detailed above, open (create one if it does not yet exist) the file named `ROOTS` in an editor. Append a line containing the `artifact_directory` path. (Note: in Windows, ensure this is in Cygwin format (see above `artifact_direcotry` section).)
Save and close the `ROOTS` file.  (Note: the name is `ROOTS` instead of `ROOT`. Also note the addition only happens in your `$ISABELLE_HOME_USER` directory, not the artifact directory.)

#### For Windows: 
Make sure no empty newlines in file `ISABELLE_HOME_USER/ROOTS`. This is known to cause issue in Isabelle.


### Execute command running artifact

#### For Linux/MacOS
In a terminal, change into `artifact_directory` using the `cd` command. Then execute:
```
isabelle jedit -l AllFixes
```

#### For Windows

In the Cygwin terminal, change into `artifact_directory` using the `cd` command. Then execute:
```
isabelle jedit -l AllFixes
```
Sometimes the build can get stuck in the middle, possibly due to Isabelle hitting the memory limits and swapping happens.
Increasing the Java heap size limit can potentially alleviate this issue:
```
isabelle jedit -l AllFixes -J -Xmx8192m
```

By default Isabelle uses a 32-bit-pointer ML system on all platforms, which limits the ML heap to 16GB. If the build runs out of memory, put the line `ML_system_64 = true` into `$ISABELLE_HOME_USER/etc/preferences` and, for example, `ML_OPTIONS="--minheap 2000 --maxheap 40000"` into `$ISABELLE_HOME_USER/etc/settings` (this is the configuration the session was last built with on a 64GB machine).

### GUI building process
Once you have entered this command, the Isabelle IDE will open, with messages starting:
```
Build started for Isabelle/AllFixes ...
Building AllFixes ...
AllFixes: theory AllFixes.Transposed
```

The process can be left running in the background. Taking roughly 3 hours on an Intel core i9 14900HX machien with 64GB RAM, it should complete with an Isabelle session called `AllFixes`. The `AllFixes` session contains necessary context for the top-level theorem (e.g., all the rule lemmas).

---

## Expected results
After the last step above, open the `TopLevelTheorem.thy` file using the prover IDE (click on the IDE top-left corner “File → Open”). Scroll to the bottom to see the main theorems and corollaries (also presented in the paper).

You should find that every theorem has gone through without error, and that no occurrences of the `sorry` keyword exist in the file. This indicates the proof has been successfully mechanically checked.

In particular, see:
- `all_transitions_coherent` (line 103),  
- `all_transitions_coherent_both` (line 337),  
- `SWMR_state_machine_CXL_cache` (line 348),  
- `SWMR_CXL_cache` (line 358),  
- `SWMR_pplus_cache` (line 376).