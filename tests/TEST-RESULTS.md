# Test results: JWS compact parser and checker

Run with `python3 tests/run_tests.py`. The record is
written by the run. Seed 20261026 for the random corpus.
The run happened on 2026-10-26/27.

## The oracle and PyJWT

PyJWT 2.15.1 was present (a venv inside the work directory, with cryptography). It built 20 tokens (HS256, RS256, ES256, and none algorithms).
Its unverified decode was compared with the oracle's parse on 20 tokens: 20 agreements, 0 differences.
Verdicts are always the oracle's (SPEC.md rules reimplemented in the harness). PyJWT built well formed tokens and cross checked decoding only.

## Counts

- Total check and request inputs: 425
- Agreements with the oracle: 425
- Failures: 0
- Of the verdict cases: 55 accepted, 360 rejected, 10 malformed requests answered error

## RFC 7515 fixed cases

The A.5 example is the RFC's unsecured (alg none) compact example; in the final RFC text A.6 and A.7 are JSON Serialization examples, not compact tokens, so the none cases use A.5. The RFC 7519 section 3.1 example token is byte for byte the A.1 token, so it is covered by the A.1 cases.

- [ok] A.1 accept (HS256 allowed, now before exp, issuer joe)
- [ok] A.1 reject (alg not allowed)
- [ok] A.1 reject (now equal to exp)
- [ok] A.1 reject (now after exp)
- [ok] A.1 reject (wrong issuer)
- [ok] A.1 accept (required claims present)
- [ok] A.1 reject (required claim missing)
- [ok] A.1 accept (no time checks, issuer checked)
- [ok] A.2 accept (RS256 allowed, now before exp, issuer joe)
- [ok] A.2 reject (alg not allowed)
- [ok] A.3 accept (ES256 allowed, now before exp)
- [ok] A.3 reject (now equal to exp)
- [ok] A.5 reject (alg none, HS256 allowed)
- [ok] A.5 reject (alg none, allowlist names none)
- [ok] A.5 reject (alg none, allowlist names none and HS256)

## Named differences and pinned readings

- An empty signature part is well formed base64url, so a token with an empty third part can pass the checks. Only alg none itself is turned away, not the empty signature.
- Claim and header name lookup reads the first copy of a repeated name (the JSON code's List.lookup order). The duplicate iss and alg cases pin this.
- The none rule is the exact name `none`. An alg of `None` is a different name and can be allowed.
- Date claims are judged by value, not by spelling: `2.0e9` and `20000000000e-1` are the whole number 2000000000, and `1e999999999` compares without ever being written out.
- PyJWT decode differences (its parser against the oracle's on well formed tokens): 0.

