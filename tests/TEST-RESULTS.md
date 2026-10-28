# Test results: JWS compact parser and checker

Written by `python3 tests/run_tests.py`, which drives the built tool `.lake/build/bin/jws`. A fresh run gives the same inputs, seed, and verdicts.

- Oracle: the SPEC.md rules reimplemented in tests/run_tests.py (Python 3.13), with tokens and decodes from PyJWT 2.15.1 (cryptography 46.0.3)
- Seed: 20261026
- Inputs: 448
- Failures: 0

## The oracle and PyJWT

Verdicts come from the oracle, which reimplements the SPEC.md rules in Python. PyJWT 2.15.1 built 20 tokens (HS256, RS256, ES256, and none algorithms), kept in tests/pyjwt_corpus.json with PyJWT's own unverified decode of each. The harness reads that file, so it needs no PyJWT to run; to rebuild the corpus, make a virtual environment from tests/requirements.txt and run tests/make_pyjwt_corpus.py (README, How to run it).
PyJWT's decode was compared with the oracle's parse on 20 tokens: 20 agreements, 0 differences.

## Counts

- Total check and request inputs: 448
- Agreements with the oracle: 448
- Of the verdict cases: 54 accepted, 384 rejected, 10 malformed requests answered error

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
- [ok] A.1 reject (signature part emptied, otherwise passing context)
- [ok] A.2 accept (RS256 allowed, now before exp, issuer joe)
- [ok] A.2 reject (alg not allowed)
- [ok] A.3 accept (ES256 allowed, now before exp)
- [ok] A.3 reject (now equal to exp)
- [ok] A.5 reject (alg none, HS256 allowed)
- [ok] A.5 reject (alg none, allowlist names none)
- [ok] A.5 reject (alg none, allowlist names none and HS256)

## Named differences and pinned readings

- Named change from the 2026-10-27 review: an empty signature part is now always turned away (SPEC rule 2). RFC 7515 never produces an empty signature for a signing algorithm, and alg none is turned away on its own, so the none case never reaches acceptance. The earlier reading accepted an empty signature part for a signing algorithm. The fixed case that pinned that reading now expects rejection, a new fixed case empties the A.1 token's signature part under an otherwise passing context and expects rejection, and generated corpus tokens with empty signature parts follow the same new rule in the oracle.
- Named change from review 1 item 1: a header or claims object that repeats a member name is turned away (SPEC rule 17; RFC 7515 section 4 and RFC 7519 section 4 allow only that or reading the last copy). The earlier reading took the first copy; the fixed cases that pinned it (duplicate iss, duplicate alg) now expect refusal, and new cases cover duplicate exp, aud, kid, a name that is never read, and a name spelled with a JSON escape. Names inside nested objects are not checked, since the slice reads no member of a nested object; a fixed case pins that.
- Named change from review 1 item 2: a header with a `crit` member, of any value, is turned away (SPEC rule 18). The slice understands no extension, and RFC 7515 section 4.1.11 makes a token invalid when `crit` names one the reader does not understand. Fixed cases cover b64, an unknown name, a URI name, an empty list, a string, null, and an escaped spelling; `crit` as a claim name is not a header member and passes.
- Named change from review 1 item 3: an accepted token is answered with the token text as received, not a canonical reprint, so its signature still matches its signing input. The RFC 7515 A.1 HMAC (with the RFC's key) was checked on the tool's answer for 3 A.1 accept cases, and on the A.1 input itself: verifies.
- The none rule is the exact name `none`. An alg of `None` is a different name and can be allowed.
- Date claims are judged by value, not by spelling: `2.0e9` and `20000000000e-1` are the whole number 2000000000, and `1e999999999` compares without ever being written out.
- PyJWT decode differences (its parser against the oracle's on well formed tokens): 0.

