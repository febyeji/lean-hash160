# lean-hash160

Pure Lean 4 implementations of SHA-256, RIPEMD-160, and Bitcoin's HASH160:

```text
HASH160(message) = RIPEMD160(SHA256(message))
```

This is a focused standalone package with no dependencies beyond Lean 4.32.0.
Its public API operates only on `ByteArray` and has no protocol-specific
runtime assumptions.

## API

```lean
import LeanHash160

#eval LeanHash160.SHA256.hash "abc".toUTF8
#eval LeanHash160.RIPEMD160.hash "abc".toUTF8
#eval LeanHash160.hash160 "abc".toUTF8
```

All three functions accept and return `ByteArray`. SHA-256 returns 32 bytes,
RIPEMD-160 and HASH160 return 20 bytes.

## Build and test

```bash
lake build
lake test
```

The tests include the published FIPS 180-4 SHA-256 vectors, published
RIPEMD-160 vectors, million-byte multi-block cases, Bitcoin HASH160 vectors,
and independently generated vectors around 56-byte padding and 64-byte block
boundaries.

## Assurance scope

These are executable, pure Lean definitions checked against published test
vectors. The repository does not yet prove that the implementations are
extensionally equal to mathematical specifications of SHA-256 or RIPEMD-160.
The implementation is not constant-time and has not received a cryptographic
security audit. Standard-conforming message lengths are below `2^64` bits.

## Provenance

The implementation history includes SHA-256 and RIPEMD-160 code adapted from
[`powdr-labs/evm-semantics`](https://github.com/powdr-labs/evm-semantics) at
commit `601183cb2d959748243d59093c144652a6f10716`. The package has since been
restructured around standalone padding, encoding, state, and compression
modules. See `NOTICE` for the required attribution.

## License

Apache License 2.0.
