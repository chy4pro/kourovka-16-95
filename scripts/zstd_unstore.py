#!/usr/bin/env python3
"""Decode raw-block Zstandard frames written by zstd_store.py to stdout."""
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("input")
args = parser.parse_args()

with open(args.input, "rb") as source:
    if source.read(6) != b"\x28\xb5\x2f\xfd\x00\x38":
        raise SystemExit("unsupported frame header")
    while True:
        raw = source.read(3)
        if len(raw) != 3:
            raise SystemExit("truncated block header")
        header = int.from_bytes(raw, "little")
        last = header & 1
        block_type = (header >> 1) & 3
        size = header >> 3
        if block_type != 0:
            raise SystemExit("non-raw block")
        payload = source.read(size)
        if len(payload) != size:
            raise SystemExit("truncated block")
        import sys
        sys.stdout.buffer.write(payload)
        if last:
            if source.read(1):
                raise SystemExit("trailing frame data")
            break
