import os

# Name of the base session
base_session_name = 'Base'

# Name of the ROOT file to be generated
root_file_name = 'ROOT'

def generate_root_file():
    # Get the list of Fix* directories in the current directory
    fix_dirs = [d for d in os.listdir('.') if os.path.isdir(d) and d.startswith('Fix')]

    # Sort the list for consistent ordering
    fix_dirs.sort()

    # Prepare the directories and theories lists
    directories = []
    theories = []

    for fix_dir in fix_dirs:
        # Add the directory to the directories list
        directories.append(f'"{fix_dir}"')

        # Assume the theory file has the same name as the directory
        theory_name = fix_dir

        # Add the theory to the theories list
        theories.append(theory_name)

    # Build the content of the ROOT file
    root_content = f'session "AllFixes" = {base_session_name} +\n'
    root_content += '  options [document = false]\n'
    root_content += '  directories\n'

    for dir_name in directories:
        root_content += f'    {dir_name}\n'

    root_content += '  theories\n'

    for theory_name in theories:
        root_content += f'    {theory_name}\n'

    # Write the ROOT file in the current directory
    with open(root_file_name, 'w') as f:
        f.write(root_content)

    print(f'ROOT file "{root_file_name}" generated successfully in the current directory.')

if __name__ == '__main__':
    generate_root_file()
