# Trying a new characteristic

Run the primary decomposition wrapper through `scripts/regenerate_ms.py`, beginning with one chart and `--start-depth 6`. Keep one solver child at a time. Any surviving complete all-bad leaf is only a candidate: solve it, print a point over the relevant extension field, and independently test all 24 column permutations with the exact cyclic oracle before drawing a conclusion.
