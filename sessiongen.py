import os
import shutil

# List of base theories
base_theories = [
    'BasicInvariants',
    'BuggyRules',
    'CoherenceProperties',
    'Transposed'
]

# Name of the base session
base_session_name = 'Base'

# Directory to store the base session
base_directory = base_session_name

# Create the base directory if it doesn't exist
if not os.path.exists(base_directory):
    os.makedirs(base_directory)

# Move base theory files to the base directory
for theory in base_theories:
    theory_file = theory + '.thy'
    if os.path.exists(theory_file):
        shutil.copy(theory_file, base_directory)

# Create the ROOT file for the base session
base_root_content = f'''session "{base_session_name}" = HOL +
  options [document = false]
  theories
    {"\n    ".join(base_theories)}
'''

with open(os.path.join(base_directory, 'ROOT'), 'w') as f:
    f.write(base_root_content)

print(f'Created base session "{base_session_name}" with theories: {", ".join(base_theories)}\n')

# Get the list of Fix*.thy files in the current directory
theory_files = [f for f in os.listdir('.') if f.startswith('Fix') and f.endswith('.thy')]

# Process each Fix*.thy file
for theory_file in theory_files:
    # Get the theory name without the .thy extension
    theory_name = theory_file[:-4]

    # Create a directory for the theory
    if not os.path.exists(theory_name):
        os.makedirs(theory_name)

    # Copy the theory file into its directory
    shutil.copy(theory_file, theory_name)

    # Create the ROOT file for the session
    root_content = f'''session "{theory_name}" = {base_session_name} +
  options [document = false]
  theories
    {theory_name}
'''

    root_path = os.path.join(theory_name, 'ROOT')
    with open(root_path, 'w') as f:
        f.write(root_content)

    print(f'Created session "{theory_name}" in directory "{theory_name}"\n')

print('All sessions have been created.')
