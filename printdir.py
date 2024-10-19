import os

# Directory where your ASPLOS25 project is located
project_directory = os.path.abspath('.')

# Get the list of subdirectories in the current directory that start with 'Fix' or 'Base'
subdirs = [d for d in os.listdir('.') if os.path.isdir(d) and (d.startswith('Fix') or d == 'Base')]

# Sort the list for consistency
subdirs.sort()

# Generate the lines to be added to the ROOTS file
root_lines = []

for subdir in subdirs:
    # Construct the full path using forward slashes
    root_line = os.path.join('~/Documents/GitHub/ASPLOS25', subdir)
    # Replace backslashes with forward slashes
    root_line = root_line.replace('\\', '/')
    root_lines.append(root_line)

# Print the lines
print('Lines to add to your ROOTS file:\n')
for line in root_lines:
    print(line)
