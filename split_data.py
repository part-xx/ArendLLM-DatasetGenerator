#!/usr/bin/env python3
"""Split data.json randomly into train.json, val.json, and test.json.

Usage:
    python split_data.py <train_fraction> <val_fraction> <test_fraction>

Example:
    python split_data.py 0.8 0.1 0.1
"""

import sys
import json
import random
import os

def parse_concatenated_json(filepath):
    """Parse a file containing concatenated JSON objects."""
    with open(filepath, 'r') as f:
        content = f.read()
    decoder = json.JSONDecoder()
    objects = []
    idx = 0
    while idx < len(content):
        # Skip whitespace
        while idx < len(content) and content[idx] in ' \t\n\r':
            idx += 1
        if idx >= len(content):
            break
        obj, end_idx = decoder.raw_decode(content, idx)
        objects.append(obj)
        idx = end_idx
    return objects

def write_concatenated_json(filepath, objects):
    """Write objects as concatenated JSON (matching original format)."""
    with open(filepath, 'w') as f:
        for obj in objects:
            json.dump(obj, f, indent=4)
            f.write('\n')

def main():
    if len(sys.argv) != 4:
        print(__doc__)
        sys.exit(1)

    train_frac = float(sys.argv[1])
    val_frac = float(sys.argv[2])
    test_frac = float(sys.argv[3])

    total = train_frac + val_frac + test_frac
    if abs(total - 1.0) > 1e-6:
        print(f"Error: fractions must sum to 1.0, got {total}")
        sys.exit(1)

    data_dir = os.path.dirname(os.path.abspath(__file__))
    input_path = os.path.join(data_dir, 'data.json')

    print(f"Parsing {input_path}...")
    objects = parse_concatenated_json(input_path)
    n = len(objects)
    print(f"Found {n} objects.")

    random.seed(42)
    random.shuffle(objects)

    train_end = int(n * train_frac)
    val_end = train_end + int(n * val_frac)

    train_data = objects[:train_end]
    val_data = objects[train_end:val_end]
    test_data = objects[val_end:]

    print(f"Train: {len(train_data)}, Val: {len(val_data)}, Test: {len(test_data)}")

    write_concatenated_json(os.path.join(data_dir, 'train.json'), train_data)
    write_concatenated_json(os.path.join(data_dir, 'val.json'), val_data)
    write_concatenated_json(os.path.join(data_dir, 'test.json'), test_data)

    print("Done.")

if __name__ == '__main__':
    main()
