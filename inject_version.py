"""Replace VERSION = "dev" with the actual build version in main.py."""
import sys

version = sys.argv[1]
with open("main.py", "r", encoding="utf-8") as f:
    content = f.read()
content = content.replace('VERSION = "dev"', f'VERSION = "{version}"')
with open("main.py", "w", encoding="utf-8") as f:
    f.write(content)
print(f"Injected version: {version}")
