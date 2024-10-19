# ASPLOS25CXLcacheFormalisation
Run the command "isabelle build -d . -d Base -j4 -vv -a" in the current directory.

If you get errors from complaining “session unknown”, you need to 
use the command "isabelle getenv ISABELLE_HOME_USER" to find our your Isabelle user profile folder and
update the file named "ROOTS" in the ISABELLE_HOME_USER folder by adding simply the path to this repo (and subdirectories):
You might want to add those lines in path_to_add.txt (replace path as necessary)

Once started the session process can be left to run on the background.

Rule files are prefixed with "Fix".

Rules are included in the "BuggyRules.thy" file.

The toplevel theorem resides in "TopLevelTheorem.thy". We only prove one direction of the transactions, using a toggle theorem to flip the proof for the other side, see "Toggle.thy"

For scenario verification, see "Litmus.thy".
