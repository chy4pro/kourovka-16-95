# Dimension-five rank-one certificates

This directory records the two independently gated encoder families for the
deflation ideal `J5`.

- `independent/` contains the clean-room encoder, its controls and finite
  audits, and all 304 input/basis pairs: characteristic zero plus every one of
  the 303 prime characteristics below 2000.
- `line/` contains the line encoder scripts, all 169 reduced bases in
  characteristic zero and the prime characteristics below 1000, and the ten
  representative expanded inputs in characteristic zero and the nine prime
  characteristics already used by the dimension-four package. The complete
  line sweep's 169 input/basis pairs are authenticated by
  `LINE_INDEX.sha256`; the other 159 duplicate expanded inputs are not copied
  into this Git tree because doing so together with the complete independent
  family would violate the ticket's 150 MB repository cap.

`GRADE.md` has first line `PASS` and is the independent gate for Claim C8.
The raw realised-pattern control hit its cap and is labeled
`UNRESOLVED-due-to-load`; it is not used as evidence. Its exact point
evaluation and the separately solved witness-containing ideal provide the
control conclusion described in `REPORT.md`.
