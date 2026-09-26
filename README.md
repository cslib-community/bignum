# Bignum

A port of parts of AWS's [s2n-bignum](https://github.com/awslabs/s2n-bignum) to Lean 4.

Our immediate goal is to port to Lean 4 the [relational Hoare algebra](https://arxiv.org/abs/2505.14348) formalism implemented in [s2n-bignum](https://github.com/awslabs/s2n-bignum) to verify correctness and performance properties of real 64-bit ARM machine code (aarch64).

Right now, we're only porting the aarch64 part.  But there are plans to port the 64-bit x86 (x86_64) part in the future.

This port will enable among other things the verification of the integer arithmetic routines included in [s2n-bignum](https://github.com/awslabs/s2n-bignum) in Lean 4.  These routines are intended for cryptographic applications and were written in pure machine code, designed to be callable from C and other high-level languages, with separate but API-compatible versions of each function for 64-bit x86 (x86_64) and ARM (aarch64).

## Building

```bash
lake build
```

## Testing

```bash
lake test
```
