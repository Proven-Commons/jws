# Test results: JWS compact parser and checker

Written by `python3 tests/run_tests.py`, which drives the built tool `.lake/build/bin/jws`. A fresh run gives the same inputs, seed, and verdicts.

- Oracle: the SPEC.md rules reimplemented in tests/run_tests.py (Python 3.13), with tokens and decodes from PyJWT 2.15.1 (cryptography 46.0.3)
- Seed: 20261026
- Inputs: 743
- Failures: 0

## The oracle and PyJWT

Verdicts come from the oracle, which reimplements the SPEC.md rules in Python. PyJWT 2.15.1 built 20 tokens (HS256, RS256, ES256, and none algorithms), kept in tests/pyjwt_corpus.json with PyJWT's own unverified decode of each. The harness reads that file, so it needs no PyJWT to run; to rebuild the corpus, make a virtual environment from tests/requirements.txt and run tests/make_pyjwt_corpus.py (README, How to run it).
PyJWT's decode was compared with the oracle's parse on 20 tokens: 20 agreements, 0 differences.

## PyJWT verdicts on the probe tokens

36 HS256 probe tokens, signed with a known key, were run through PyJWT's `jwt.decode` (with that key and each probe's algorithms, issuer, audience and required claims, at the time 1793208734) when the corpus was built, and through the tool at the same time. The expected verdicts are the oracle's; PyJWT's are compared beside them. 28 agree. Each disagreement is named below with its reason; an unnamed one, or a named one that no longer differs, is a failure.

- duplicate alg, none then HS256: this slice rejects, PyJWT accepts. PyJWT reads the last copy of a repeated name, which RFC 7515 section 4 and RFC 7519 section 4 allow; this slice turns any repeat away, which they also allow (SPEC rule 17).
- duplicate alg spelled with an escape: this slice rejects, PyJWT accepts. PyJWT reads the last copy of a repeated name, which RFC 7515 section 4 and RFC 7519 section 4 allow; this slice turns any repeat away, which they also allow (SPEC rule 17).
- duplicate iss, joe then evil, issuer evil: this slice rejects, PyJWT accepts. PyJWT reads the last copy of a repeated name, which RFC 7515 section 4 and RFC 7519 section 4 allow; this slice turns any repeat away, which they also allow (SPEC rule 17).
- duplicate exp, expired then live: this slice rejects, PyJWT accepts. PyJWT reads the last copy of a repeated name, which RFC 7515 section 4 and RFC 7519 section 4 allow; this slice turns any repeat away, which they also allow (SPEC rule 17).
- duplicate name nobody reads: this slice rejects, PyJWT accepts. PyJWT reads the last copy of a repeated name, which RFC 7515 section 4 and RFC 7519 section 4 allow; this slice turns any repeat away, which they also allow (SPEC rule 17).
- b64 false without crit: this slice accepts, PyJWT rejects (DecodeError). PyJWT implements RFC 7797 and reads the payload as unencoded; this slice understands no extension and, as RFC 7515 section 4 asks of a parameter a reader does not understand, ignores b64 when crit does not list it (SPEC rule 18).
- iat in the future: this slice accepts, PyJWT rejects (ImmatureSignatureError). PyJWT refuses an iat after the current time; RFC 7519 section 4.1.6 sets no such check, and this slice reads iat for its type only (SPEC rule 12).
- exp a string: this slice rejects, PyJWT accepts. PyJWT converts the string to a number; RFC 7519 makes exp a NumericDate, a JSON number, and this slice turns a string away (SPEC rule 9).

## Counts

- Total check and request inputs: 743
- Of these: 20 PyJWT-built tokens under 5 contexts each, 36 PyJWT verdict probes, 240 random corpus cases (seed 20261026), 240 shape corpus cases (seed 20261027), and 127 fixed and mutation cases
- Agreements with the oracle: 743
- Of the verdict cases: 105 accepted, 628 rejected, 10 malformed requests answered error

## RFC 7515 fixed cases

The A.5 example is the RFC's unsecured (alg none) compact example; in the final RFC text A.6 and A.7 are JSON Serialization examples, not compact tokens, so the none cases use A.5. The RFC 7519 section 3.1 example token is byte for byte the A.1 token, so it is covered by the A.1 cases. A.4 (ES512) signs the payload `Payload`, which is not JSON: this slice reads JWTs, whose payload is a JSON claims set, so A.4 is a named departure from RFC 7515 and its fixed case expects refusal.

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
- [ok] A.4 reject (ES512 allowed; payload "Payload" is not JSON, a JWS this JWT checker leaves out)
- [ok] A.5 reject (alg none, HS256 allowed)
- [ok] A.5 reject (alg none, allowlist names none)
- [ok] A.5 reject (alg none, allowlist names none and HS256)

## Named differences and pinned readings

- Named change from the 2026-10-27 review: an empty signature part is now always turned away (SPEC rule 2). RFC 7515 never produces an empty signature for a signing algorithm, and alg none is turned away on its own, so the none case never reaches acceptance. The earlier reading accepted an empty signature part for a signing algorithm. The fixed case that pinned that reading now expects rejection, a new fixed case empties the A.1 token's signature part under an otherwise passing context and expects rejection, and generated corpus tokens with empty signature parts follow the same new rule in the oracle.
- Named change from review 1 item 1: a header or claims object that repeats a member name is turned away (SPEC rule 17; RFC 7515 section 4 and RFC 7519 section 4 allow only that or reading the last copy). The earlier reading took the first copy; the fixed cases that pinned it (duplicate iss, duplicate alg) now expect refusal, and new cases cover duplicate exp, aud, kid, a name that is never read, and a name spelled with a JSON escape. Names inside nested objects are not checked, since the slice reads no member of a nested object; a fixed case pins that.
- Named change from review 1 item 2: a header with a `crit` member, of any value, is turned away (SPEC rule 18). The slice understands no extension, and RFC 7515 section 4.1.11 makes a token invalid when `crit` names one the reader does not understand. Fixed cases cover b64, an unknown name, a URI name, an empty list, a string, null, and an escaped spelling; `crit` as a claim name is not a header member and passes.
- Named change from review 1 item 3: an accepted token is answered with the token text as received, not a canonical reprint, so its signature still matches its signing input. The RFC 7515 A.1 HMAC (with the RFC's key) was checked on the tool's answer for 3 A.1 accept cases, and on the A.1 input itself: verifies.
- Named change from review 1 item 6: with no expected audience, a token that carries `aud` is turned away (SPEC rule 16). RFC 7519 section 4.1.3 asks a reader that does not identify itself with a value in `aud` to reject the token. PyJWT reads it the same way; some other libraries accept such a token. Generated tokens with `aud` under a context with no audience now expect refusal in the oracle.
- From review 1 item 9: the allowlist does not stop key and algorithm confusion. The page warns that a caller's signature checker must use each key with exactly one algorithm (RFC 8725 section 3.1) and that an allowlist should name one family. The generated contexts here mix families only as test data for the allowlist rule.
- The none rule is the exact name `none`. An alg of `None` is a different name and can be allowed.
- Named change from review 1 item 7: `exp`, `nbf` and `iat` may be non-integers (RFC 7519 section 2) and are compared exactly with the current time (SPEC rule 9). The earlier reading turned every fractional date away; the three fixed cases that pinned it now expect acceptance, and new cases cover fractions a millionth either side of now, equality, `nbf`, and exponents of -999999999.
- Date claims are judged by value, not by spelling: `2.0e9` and `20000000000e-1` are the number 2000000000, and `1e999999999` compares without ever being written out.
- PyJWT decode differences (its parser against the oracle's on well formed tokens): 0.

