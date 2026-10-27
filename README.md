# jws: a JWS compact parser and checker, with a proved round trip

A parser and checker for the JWS compact form (RFC 7515) in Lean, with the plan's main claim proved: printing a parsed token gives the token back. The parser reads the three base64url parts, decodes the header and payload as JSON, and holds the signature bytes unchanged. The checker runs the shape and claims rules of `SPEC.md` (algorithm allowlist, required claims, and the `exp`, `nbf`, `iss`, and `aud` claims against a caller supplied context). Tests run the RFC 7515 Appendix A examples and a differential corpus against an oracle implementing the same rules; see `tests/TEST-RESULTS.md` for the counts.

Status: in progress. The first slice from plan issue 1 has landed locally. The specification has not yet been approved by a reviewer apart from its author, and no statement file (`Spec.lean`) has been added by a reviewer, so this is not verified.

## Limit, stated up front

This slice does not verify a signature. It must never be described as a verified token on its own. Signature verification is the second slice. A caller that reads claims from this slice without verifying the signature has not checked authenticity.

## Where the JSON code came from

The JSON parser, printer, value type, and round trip proof are the json repo's, carried in unchanged under `Json/` and `Proofs/RoundTrip.lean` (the repos in this org do not import each other). Everything else is new here: the base64url codec (`Jws/Base64url.lean`), a strict UTF-8 codec (`Jws/Utf8.lean`), and the token framing, claims reading, and checker (`Jws/Token.lean`). The base64url code follows the shape of the codec repo's Base64 work, with the URL safe alphabet and no padding.

## What is proved

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a token gives the token back, for tokens whose JSON parts are well formed in the json slice's sense. | `Jws.Proofs.parseToken_print` |
| Decoding the base64url encoding of any bytes gives the bytes back. | `Jws.Base64url.Proofs.decode_encode` |
| Encoding the decoding of any text the decoder accepts gives the text back. | `Jws.Base64url.Proofs.encode_decode` |
| Decoding the UTF-8 encoding of any text gives the text back. | `Jws.Utf8.Proofs.decode_encode` |
| Parsing the canonical printed form of a well formed JSON value gives the value back (carried in with the JSON code). | `Json.Proofs.parse_print` |

The two base64url round trips check against `propext` and `Quot.sound` only. The token and UTF-8 round trips check against the standard three (`propext`, `Classical.choice`, `Quot.sound`). A reader can confirm with `#print axioms` on each name.

## What is not proved

- That the checker accepts exactly the tokens `SPEC.md` says it should. The acceptance rules live in one function (`Jws.accept`) and their completeness rests on the tests: the RFC examples, the mutation cases, and the differential corpus against the harness oracle.
- Signature verification, as stated above: nothing about keys, signing inputs, or any algorithm.
- The reverse printing direction at the token level (printing a parsed token is how the round trip is stated; the base64url and JSON layers each prove their own reverse directions).
- Anything about the numeric meaning of claims beyond the exact decimal reading the checker itself uses (whole seconds, comparisons). The reading code is exercised by the tests, including exponent spellings and very large exponents.
- Reading requests and printing answers in `Main.lean`: line splitting, the field format, the decimal code reading. The tests cover them, malformed requests included.
- Speed. The code works on lists, which suits proofs, not large tokens.

Two readings worth naming, both stated in `SPEC.md` and pinned by tests:

- An empty signature part is well formed, so it can pass the checks. Only the algorithm name `none` is turned away outright, together with any context whose allowlist names `none`.
- When a JSON object repeats a name, lookup reads the first copy, as the JSON code's lookup does.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- For the tests: Python's standard library (the oracle's JSON reading and exact decimals), PyJWT and cryptography in the test venv when present (token building and decode cross checks only; verdicts never come from PyJWT), and the RFC 7515 text for the fixed examples. The results file names the versions used.

This project has no dependencies beyond Lean itself. The test harness's PyJWT corpus is optional and lives in a venv inside the work directory.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan). Build, then feed request lines to the tool:

```
lake build
python3 tests/run_tests.py
```

A request is one `check` line; `SPEC.md` states the field format in full. The token text, the current time, the allowlist, the required claims, the expected issuer, and the expected audience are the six fields, each written as comma separated decimal character codes, the fields separated by semicolons. The answer is `ok:` and the codes of the canonical reprinted token, `none` when the token is not accepted, and `error` when the request is malformed.

## Re-check it

Needs Linux, elan, and Python 3.11 or later.

```
lake build
grep -rn "sorry" --include="*.lean" Json Jws Proofs Main.lean Json.lean Jws.lean Proofs.lean
python3 tests/run_tests.py
```

The grep should print nothing: there is no `sorry` anywhere. The test script runs the fixed RFC cases, the mutation cases, the malformed request cases, and the differential corpus (PyJWT built tokens when the venv is present, plus a seeded random corpus), and writes the counts to `tests/TEST-RESULTS.md`.
