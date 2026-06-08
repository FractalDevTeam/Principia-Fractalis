#!/usr/bin/env python3
import os
import re

results = []
for root, dirs, files in os.walk('.'):
    if '.lake' in root:
        continue
    for file in files:
        if file.endswith('.lean'):
            filepath = os.path.join(root, file)
            try:
                with open(filepath, 'r') as f:
                    lines = f.readlines()
                    count = 0
                    for line in lines:
                        # Skip comment lines
                        if line.strip().startswith('--') or line.strip().startswith('/-'):
                            continue
                        # Count actual sorry/admit statements
                        if re.search(r'\bsorry\b|\badmit\b', line):
                            count += 1
                    if count > 0:
                        results.append((count, filepath))
            except:
                pass

results.sort(reverse=True)
total = 0
for count, filepath in results:
    print(f"{count:3d} actual sorrys/admits - {filepath}")
    total += count
print(f"\n{total:3d} TOTAL ACTUAL SORRYS/ADMITS")
