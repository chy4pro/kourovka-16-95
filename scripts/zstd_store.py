#!/usr/bin/env python3
"""Write a standards-compliant Zstandard frame using raw blocks.

This dependency-free fallback is for release assembly on hosts without the
zstd executable. It does not reduce size, but its output is a valid .zst
stream and can be decoded by ordinary Zstandard tools.
"""
import argparse
import struct
import sys

parser = argparse.ArgumentParser()
parser.add_argument("output")
args = parser.parse_args()

with open(args.output, "wb") as target:
    target.write(b"\x28\xb5\x2f\xfd")
    target.write(b"\x00\x38")  # no content-size field; 128 KiB window
    previous = sys.stdin.buffer.read(128 * 1024)
    if not previous:
        target.write(b"\x01\x00\x00")
    while previous:
        following = sys.stdin.buffer.read(128 * 1024)
        header = (len(previous) << 3) | (1 if not following else 0)
        target.write(struct.pack("<I", header)[:3])
        target.write(previous)
        previous = following
