import os

def collect_claude_md(root_dir, output_file):
    with open(output_file, 'w', encoding='utf-8') as out:
        for dirpath, _, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename == "CLAUDE.md":
                    rel_path = os.path.relpath(os.path.join(dirpath, filename), root_dir)
                    out.write(f"--- {rel_path} ---\n")
                    try:
                        with open(os.path.join(dirpath, filename), 'r', encoding='utf-8') as f:
                            out.write(f.read().strip() + "\n\n")
                    except Exception as e:
                        out.write(f"[Error reading {rel_path}: {e}]\n\n")

if __name__ == "__main__":
    root = input("Enter root directory path: ").strip()
    output = input("Enter output file name (e.g., combined.md): ").strip()
    collect_claude_md(root, output)
    print("Done.")
