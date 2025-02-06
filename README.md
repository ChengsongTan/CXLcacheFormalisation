# Artifact Appendix

## A.1 Abstract
This artifact consists of the formal model of the cache coherence protocol of Compute Express Link (CXL)–CXL.cache. It contains the model and proof of the Single-Writer-Multiple-Reader (SWMR) property of CXL.cache in the Isabelle/HOL proof assistant, as described in the paper “Formalising CXL Cache Coherence”. The protocol is modelled as a transition system over system state, where a system state comprises cacheline states, communication channels, buffers and other auxiliary structures.

---

## A.2 Artifact check-list (meta-information)
- **Algorithm**: CXL.cache Cache Coherence Protocol  
- **Program**: Isabelle theories  
- **Compilation**: `isabelle jedit`  
- **Run-time environment**: For Windows, double-click the “Cygwin-Terminal.bat” file in the installation folder, and run the command (in the Execution step) from that terminal.  For Linux/MacOS run from any terminal.
- **Execution**:  
  - First change into the artifact top-level directory.  
  - Then run the command `isabelle jedit -l AllFixes` in the artifact top-level directory.  
- **Output**: Messages shown on the proof state panel indicating theory files have been successfully processed.  
- **How much time is needed to prepare workflow (approximately)?**: 10 minutes  
- **How much time is needed to complete experiments (approximately)?**: 3 hours  
- **Publicly available?**: Yes  
- **Workflow automation framework used?**: Isabelle sessions  

---

## A.3 Description
The file that contains the definitions of the system state with type-1 devices (corresponding to the datatype definition in Figure 3 in section 3) is `Transposed.thy` (see line 157 the record definition `Type1State`). Together with the record type, some functions for manipulating certain fields of `Type1State` are also defined. The transition rules as shown in Figure 4 in section 3 of the system are defined in the file `BuggyRules.thy`.

The coherence property that is shown to be an inductive invariant of the system lies in `CoherenceProperties.thy` (see line 199, definition `SWMR_state_machine`).

The `BasicInvariants.thy` file contains some basic invariants related to certain transitions and functions we already defined in `BuggyRules.thy` and `Transposed.thy`.

The proofs are in the rest of the `.thy` files in this artifact. Each transition rule is proven to maintain the inductive property (`SWMR_state_machine`). Since `SWMR_state_machine` is quite large (consisting of around 800 conjuncts), the proof of just a single rule is lengthy, each spanning more than 1,000 lines. They are therefore each stored in a dedicated file, where the filename corresponds to the name of the rule (up to a prefix).

As an example, the `FixSIAGO_WritePull.thy` file contains the proof that the `SIAGO_WritePull` rule maintains the `SWMR_state_machine` property. The main lemma stating this fact is at the end of the file (line 2915 with name `SIAGO_WritePull_coherent`).

The most important auxiliary lemma leading to this is `SIAGO_WritePull’_coherent_aux_simpler` (line 233). This auxiliary lemma breaks down the proof into hundreds of subgoals. We call lemmas like this “rule lemmas” as they each correspond to a rule.

The top-level theorem stating the Single-Writer-Multiple-Reader property of the transition system is the corollary `SWMR_pplus_cache` in `TopLevelTheorem.thy` (line 354), corresponding to Theorem 6.2 in the paper. Some main theorems lead to this corollary:
- If `initial_state(𝑇)` then `SWMR_state_machine(𝑇)` (Theorem `SWMR_state_machine_CXL_cache` at line 321).  
- If `𝑇 −→ 𝑇’` and `SWMR_state_machine(𝑇)` then `SWMR_state_machine(𝑇’)` (Theorem `all_transitions_coherent` at line 103).  

These two theorems correspond to the first two of the three properties described in the paper just before Theorem 6.

### A.3.1 How to access
The artifact is available on GitHub:  
<https://github.com/ChengsongTan/CXLcacheFormalisation>

### A.3.2 Software dependencies
The artifact depends on Isabelle2023, available at:  
<https://isabelle.in.tum.de/website-Isabelle2023/index.html>

---


---

## Running Experiment

### Preparing suitable running environment
#### For Windows:
Download Isabelle2023 (see above URL). Double-click the downloaded installer to complete the installation process; it is suggested to put Isabelle2023 in some easy-to-access folder such as the desktop so it is easy to navigate there (needed later).
##### Potential issues with downloading and installing Isabelle2023 on Windows
Tested on Windows Server 2022 (Desktop Experience)

(a) If you use Edge and you're not given permission to open the file (e.g. Edge says `Isabelle2023.exe isn't commonly downloaded ...`), do the following:

Click three dots (more actions) > Keep > Show more > Keep anyway. Confirm that we can now execute Isabelle2023.exe.

(b) If Isabelle shows `IO error … (access is denied)`, ignore it & just close Isabelle.

Clone or download the artifact from GitHub (see above URL). If you downloaded a zip of the artifact, uncompress this zip file.

#### For Linux: 
Download using this address:
```
https://isabelle.in.tum.de/website-Isabelle2023/dist/Isabelle2023_linux.tar.gz
```

Then run the command from the command line in the folder where the downloaded file is stored:
```
tar -xzf Isabelle2023_linux.tar.gz
```


To be able to execute the `isabelle` command in the artifact folder, run these commands to add the path to your Isabelle bin directory to your PATH variable:
```
echo 'export PATH=$PATH:/home/ubuntu/Downloads/Isabelle2023/bin' >> ~/.bashrc
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
/home/ubuntu/.isabelle/Isabelle2023
```

#### For Windows
In the Windows explorer, go to the folder where Isabelle2023
is installed and double-click the "Cygwin-Terminal.bat" file
to open a Cygwin terminal (a minimal installation of Cygwin
ships with Isabelle).
In the Cygwin terminal, run `isabelle getenv ISABELLE_HOME_USER`. This will lead to the path of a directory being output, e.g.
```
/cygdrive/c/Users/Joe/.isabelle/Isabelle2023
```
Navigate to the directory. If you use Windows Explorer and the path is `cygdrive/c/...`, this means `c/...` "


### Run the workflow: preparation
After navigating to the directory as detailed above, open (create one if it does not yet exist) the file named `ROOTS` in an editor. Append a line containing the `artifact_directory` path. (Note: in Windows, ensure this is in Cygwin format (see above `artifact_direcotry` section).)
Save and close the `ROOTS` file.  

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
Increasing the heap size limit can potentially alleviate this issue:
```
isabelle jedit -l AllFixes -J -Xmx8192m
```

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
- `SWMR_state_machine_CXL_cache` (line 321),  
- `SWMR_CXL_cache` (line 336),  
- `SWMR_pplus_cache` (line 354).