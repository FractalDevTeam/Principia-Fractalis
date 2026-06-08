#!/usr/bin/env python3
import os
import subprocess

results = []
for root, dirs, files in os.walk('.'):
    if '.lake' in root:
        continue
    for file in files:
        if file.endswith('.lean'):
            filepath = os.path.join(root, file)
            try:
                with open(filepath, 'r') as f:
                    content = f.read()
                    count = content.count('sorry')
                    if count > 0:
                        results.append((count, filepath))
            except:
                pass

results.sort(reverse=True)
total = 0
for count, filepath in results:
    print(f"{count:3d} sorrys - {filepath}")
    total += count
print(f"\n{total:3d} TOTAL SORRYS")
