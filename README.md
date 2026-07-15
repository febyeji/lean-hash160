# lean-hash160

Pure Lean 4 implementations of SHA-256, RIPEMD-160, and Bitcoin's HASH160:

```text
HASH160(message) = RIPEMD160(SHA256(message))
```

The package is intentionally small, has no dependencies beyond Lean, and is
compatible with Lean 4.16.0.

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
RIPEMD-160 vectors, million-byte multi-block cases, and Bitcoin HASH160 vectors.

## Assurance scope

These are executable, pure Lean definitions checked against published test
vectors. The repository does not yet prove that the implementations are
extensionally equal to mathematical specifications of SHA-256 or RIPEMD-160.
The implementation is not constant-time and has not received a cryptographic
security audit.

## Provenance

The SHA-256 and RIPEMD-160 implementations are adapted from
[`powdr-labs/evm-semantics`](https://github.com/powdr-labs/evm-semantics) at
commit `601183cb2d959748243d59093c144652a6f10716`. See `NOTICE` for details.

## License

Apache License 2.0.
