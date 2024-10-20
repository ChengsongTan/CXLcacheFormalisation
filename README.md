# ASPLOS25CXLcacheFormalisation


You can explore all thy files in this directory.
## Important: this works with Isabelle2023
For looking at toplevel theorem, go to TopLevelTheorem.thy.

You can either check it via directly running Isabelle jedit (which will likely crash because too many files are imported), or build sessions prepared in the ROOT file and then load them with TopLevelTheorem.thy (recommended).


## Building the sessions for all rules
Run the command `isabelle jedit -l AllFixes` in the current directory.

If you get errors from complaining “session unknown”, you need to 
use the command `isabelle getenv ISABELLE_HOME_USER` to find our your Isabelle user profile folder and
update the file named "ROOTS" in the ISABELLE_HOME_USER folder by adding simply the path to this repo (and subdirectories):
You might want to add those lines in path_to_add.txt (replace path as necessary)

Once started the session process can be left to run on the background.

After the build finished, open  the `TopLevelTheorem.thy` file to view the main theorem of the paper.

## Files to look at
Rule files are prefixed with "Fix".

Rules are included in the `BuggyRules.thy` file.

The toplevel theorem resides in `TopLevelTheorem.thy`. We only prove one direction of the transactions, using a toggle theorem to flip the proof for the other side, see `Toggle.thy`

For scenario verification, see `Litmus.thy`.
