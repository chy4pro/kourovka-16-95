# Pinned software

- **msolve 0.10.1.** Audited source checkout commit `1e3af01f3864f6c848814b02a450f384c108adea`; upstream source snapshot URL: `https://github.com/algebraic-solving/msolve/archive/1e3af01f3864f6c848814b02a450f384c108adea.tar.gz`. The canonical uncompressed `git archive --format=tar --prefix=msolve-0.10.1/` SHA-256 is `bbbe6785ef5efbd5e5f46c9a07963523ca18a973a2226f65eb25eef3c7bebe54`. Build: `./configure --prefix=PREFIX CFLAGS=-O2 CPPFLAGS=-IPREFIX/include LDFLAGS='-LPREFIX/lib -Wl,-rpath,PREFIX/lib' && make -j2 && make install`. Certificate invocation: `msolve -g 2 -t 1`.
- **Singular 4.3.2.** Optional only for lift/cofactor tooling; it is not part of the certificate acceptance path. Source: `https://github.com/Singular/Singular/releases/tag/Release-4-3-2`.
- **Lean:** `leanprover/lean4:v4.34.0-rc1` from `lean/lean-toolchain`.
- **Mathlib:** commit `de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11` from `lean/lake-manifest.json`.
- **Python/SymPy used for assembly checks:** Python 3.9.6 and SymPy 1.14.0. Scripts require Python 3.9 or newer.
