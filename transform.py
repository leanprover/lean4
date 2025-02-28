import subprocess
import re
import os

def get_changed_files():
    """Get all files modified in the latest commit."""
    # Get list of files changed in the last commit
    cmd = ['git', 'diff-tree', '--no-commit-id', '--name-only', '-r', 'HEAD']
    files = subprocess.check_output(cmd, text=True).splitlines()
    return files

def transform_spelling_line(line):
    """Transform a recommended_spelling line from old to new format."""
    pattern = r'recommended_spelling "([^"]+)" "([^"]+)" (.*)'
    match = re.match(pattern, line.strip())
    
    if match:
        symbol, name, terms = match.groups()
        term_list = [t.strip() for t in terms.split()]
        terms_formatted = ", ".join(term_list)
        return f'recommended_spelling "{name}" for "{symbol}" in [{terms_formatted}]'
    
    return line

def modify_file(file_path):
    """Apply changes to a file."""
    try:
        with open(file_path, 'r') as f:
            lines = f.readlines()
        
        modified = False
        for i, line in enumerate(lines):
            if 'recommended_spelling' in line:
                old_line = line.strip()
                new_line = transform_spelling_line(old_line)
                if old_line != new_line:
                    lines[i] = new_line + '\n'
                    modified = True
        
        if modified:
            with open(file_path, 'w') as f:
                f.writelines(lines)
            return True
        return False
    except Exception as e:
        print(f"Error processing {file_path}: {str(e)}")
        return False

def main():
    # Get all files changed in the latest commit
    changed_files = get_changed_files()
    
    # Track modified files
    modified_files = []
    
    # Process each changed file
    for file_path in changed_files:
        if os.path.exists(file_path):
            if modify_file(file_path):
                modified_files.append(file_path)
    
    # Report results
    if modified_files:
        print("Modified files:")
        for file in modified_files:
            print(f"- {file}")
    else:
        print("No files were modified.")

if __name__ == "__main__":
    main()
