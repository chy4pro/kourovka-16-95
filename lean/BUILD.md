# Lean rebuild

From this directory:

```sh
lake build
for f in K1695/*.lean; do lake env lean "$f"; done
```

No Lean build was run while assembling this package. The three prior successful axiom-audit logs are preserved in `recorded_checks/`; `AXIOMS.txt` explains what they establish.
