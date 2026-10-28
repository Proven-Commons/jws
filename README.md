# jws: a JWT parser and claims checker for the JWS compact form

Status: in progress

A parser and claims checker, in Lean, for JSON Web Tokens
(RFC 7519) in the JWS compact form (RFC 7515). The payload
must be a JSON object, a JWT claims set: RFC 7515 lets a
JWS carry any payload bytes, and a JWS whose payload is
not JSON, such as RFC 7515's own Appendix A.4 example
(payload `Payload`), does not parse here. The parser
reads the three base64url parts, keeps the first two
exactly as received (they are the signing input a
signature verifier needs), decodes the header and payload
as JSON, and holds the signature bytes unchanged. The
checker runs the shape and claims rules of `SPEC.md`: no
repeated member names in the header or the claims, no
`crit` in the header, the algorithm against a caller
allowlist, the required claims, and the `exp`, `nbf`,
`iss`, and `aud` claims against a context the caller
supplies. The definitions are in `Jws/Base64url.lean`
(the base64url codec), `Jws/Utf8.lean` (a strict UTF-8
codec), and `Jws/Token.lean` (the framing, the claims
reading, and the checker). The JSON parser, printer, value type, and
round trip proof are the json repo's, carried in unchanged
under `Json/` and `Proofs/RoundTrip.lean`, because the
repos in this org do not import each other. The rules are
written out in `SPEC.md`.

The statements a reviewer approves are in `Spec.lean`,
with the definitions in `Spec/Defs.lean` that give the
decimal value of a JSON number text, and their proofs in
`Proofs/SpecProofs.lean`. No reviewer has approved them
yet, so this project is not called verified.

One limit stands up front: this slice does not verify a
signature. A token that passes every check is well formed
and its claims are consistent with the check context; it
is not thereby verified, and it must never be described as
a verified token on its own. Signature verification is
the second slice.

The algorithm allowlist does not stop key and algorithm
confusion, such as an RSA public key used as an HMAC
secret. The caller's signature checker must use each key
with exactly one algorithm (RFC 8725 section 3.1), and an
allowlist should name algorithms of one family only (for
example `HS256` alone, or `RS256,RS384`), not HMAC and
public key algorithms together.

## How to run it

`lake build` builds the libraries, the proofs, and the
command line tool. The tool reads one request per line:
the word `check`, a space, and six fields separated by
semicolons. Each field is text written as comma separated
decimal character codes: the token text, the current time
(or empty for no time comparisons), the allowed
algorithms, the required claims, the expected issuer, and
the expected audience. It answers `ok:` and the codes of
the token text as received when the token is accepted,
`none` when it is not, and `error` when the request itself
is malformed. `SPEC.md` states the field format in full.

```
lake build
python3 tests/run_tests.py
```

`python3 tests/run_tests.py` runs the fixed RFC 7515
Appendix A cases, the mutation cases, the malformed
request cases, a seeded random corpus, and a seeded
corpus of the shapes the rules turn on (repeated names,
`crit`, whitespace and CR LF, escapes, fractional dates,
`aud`), each against an oracle implementing the same
rules. It also runs tokens PyJWT built, and HS256 probe
tokens on which PyJWT gave its own verdict, compared
beside the oracle's with every difference named. It
writes the counts to `tests/TEST-RESULTS.md` and needs
only the Python standard library: the PyJWT tokens and
verdicts are committed in `tests/pyjwt_corpus.json`, so
every run reads the same inputs. To rebuild that file
with the pinned PyJWT and cryptography:

```
python3 -m venv venv
venv/bin/pip install -r tests/requirements.txt
venv/bin/python tests/make_pyjwt_corpus.py
```

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Printing a parsed token gives back the text that was parsed, byte for byte. | `Spec.printToken_parse` |
| A parsed token holds the first two parts of the text as received, the header and claims values those parts decode to (the base64url decoder, the UTF-8 decoder, then the JSON parser), and signature bytes whose base64url is the third part; the text has exactly those three parts. The two decoders are strict, as the rows below prove. | `Spec.parseToken_reads` |
| Parsing the printed form of a token made with `Jws.makeToken` from header and claims values gives that token back, for values that are well formed in the json slice's sense. | `Spec.parseToken_print` |
| Decoding the base64url encoding of any bytes gives the bytes back. | `Spec.decode_encode` |
| Encoding what the base64url decoder returned gives the decoded text back: the decoder accepts only the canonical, unpadded encoding of its bytes. | `Spec.encode_decode` |
| Decoding the UTF-8 encoding of any text gives the text back. | `Spec.utf8_decode_encode` |
| Encoding what the UTF-8 decoder returned gives the decoded bytes back: the decoder accepts only the standard encoding of its text, each character in its shortest form, so no overlong form, no encoded surrogate, and nothing above U+10FFFF. | `Spec.utf8_encode_decode` |
| The UTF-8 decoder turns away the overlong forms C0 80, E0 80 80 and F0 80 80 80, the encoded surrogate ED A0 80, F4 90 80 80 (above U+10FFFF), a stray continuation byte 80, the truncated E2 82, and the five byte lead F8. | `Spec.utf8_rejects_ill_formed` |
| The RFC 7515 A.1 token is accepted when HS256 is allowed and the issuer must be `joe`, with no current time supplied. | `Spec.accepts_rfc_a1` |
| A hand built token with header `{"alg":"HS256"}`, claims `{"iss":"joe","exp":2000000000}`, and a 32 byte signature is accepted under HS256 allowed, current time 1500000000, and issuer `joe`. | `Spec.accepts_hand_built` |
| The RFC 7515 A.5 unsecured token (algorithm `none`, empty signature part) is refused when HS256 is the allowed algorithm. | `Spec.rejects_unsecured_none` |
| The A.5 token is refused when the allowlist itself names `none`. Such a context refuses every token: `Spec.accept_sound` proves that the context of an accepted token has no `none` on its allowlist. | `Spec.rejects_unsecured_none_when_allowlist_names_none`, `Spec.accept_sound` |
| The A.5 token is refused when the allowlist names `none` alongside HS256. | `Spec.rejects_unsecured_none_when_allowlist_mixes_none` |
| The A.1 token with its signature part emptied is refused, under a context that accepts the token as it stands. In general, an accepted token's signature is not empty (`Spec.accept_sound`). | `Spec.rejects_empty_signature`, `Spec.accept_sound` |
| The A.1 token is refused when its algorithm, HS256, is outside the allowlist (RS256 alone). In general, an accepted token's `alg` is on the allowlist (`Spec.accept_sound`). | `Spec.rejects_alg_outside_allowlist`, `Spec.accept_sound` |
| The hand built token with a padding character `=` after its first part does not parse. In general, every part of a parsed token is the canonical, unpadded base64url encoding of its bytes (`Spec.parseToken_reads` with `Spec.encode_decode`). | `Spec.rejects_part_not_base64url`, `Spec.parseToken_reads`, `Spec.encode_decode` |
| The hand built token whose header part decodes to the JSON array `["HS256"]` is refused. In general, an accepted token's header is a JSON object (`Spec.accept_sound`). | `Spec.rejects_header_not_object`, `Spec.accept_sound` |
| When the check accepts a token, under any context: the allowlist does not name `none`; the signature is not empty; the header and the claims are JSON objects with no repeated member name; the header has no `crit` member; the header's `alg` is a string other than `none`, on the allowlist; every required claim is present; `exp`, `nbf` and `iat`, when present, are JSON numbers, and when a current time is given it is before `exp` and not before `nbf`, as the checker's decimal comparison (`Jws.NumVal.cmp` on `Jws.numVal`) orders them, which `Spec.numVal_cmp_now` below proves exact; `iss`, when present, is a string; `aud`, when present, is a string or an array of strings; when an issuer is expected, `iss` is that string; when no audience is expected there is no `aud`; and when one is, `aud` is that string or an array holding it. | `Spec.accept_sound` |
| When the check accepts a token, under any context, its header and its claims are JSON objects and neither repeats a member name. | `Spec.accept_names_unique` |
| The token `eyJhbGciOiJIUzI1NiIsImFsZyI6Im5vbmUifQ.eyJleHAiOjIwMDAwMDAwMDB9.AQID`, whose header is `{"alg":"HS256","alg":"none"}`, parses and is refused under every context. | `Spec.rejects_duplicate_alg` |
| The token whose claims are `{"iss":"joe","exp":2000000000,"iss":"evil"}` (header `{"alg":"HS256"}`, signature bytes 01 02 03) parses and is refused under every context. | `Spec.rejects_duplicate_iss` |
| When the check accepts a token, under any context, its header is a JSON object with no `crit` member. | `Spec.accept_no_crit` |
| The token `eyJhbGciOiJIUzI1NiIsImI2NCI6ZmFsc2UsImNyaXQiOlsiYjY0Il19.eyJleHAiOjIwMDAwMDAwMDB9.AQID`, whose header is `{"alg":"HS256","b64":false,"crit":["b64"]}`, parses and is refused under every context. | `Spec.rejects_crit_b64` |
| The token `eyJhbGciOiJIUzI1NiJ9.eyJleHAiOjIwMDAwMDAwMDAuNX0.AQID`, whose claims are `{"exp":2000000000.5}`, parses and is accepted at the current time 2000000000 with HS256 allowed: a fractional expiry is compared exactly. | `Spec.accepts_fractional_exp_before` |
| The same token is refused at the current time 2000000001, after it expired. | `Spec.rejects_fractional_exp_after` |
| `Jws.NumVal.cmp`, the comparison the date rules use, compares exact decimal values: for any power of ten `10^m` with `m` at most both exponents, it orders two number values as their values written as whole numbers over `10^m` (`Spec.atBase`, in `Spec/Defs.lean`). | `Spec.cmp_exact` |
| `Jws.numVal` reads every number text of the JSON grammar (an optional minus sign, integer digits, optional fraction digits, an optional exponent part) and gives the text's decimal value: the sign, the integer and fraction digits read as one whole number (`Spec.digitsValue`), and ten to the exponent (`Spec.expValue`) less the count of fraction digits. | `Spec.numVal_value` |
| The comparison the `exp` and `nbf` rules make between the current time and a claim's number text of the JSON grammar is the exact comparison of the whole number with the text's decimal value. | `Spec.numVal_cmp_now` |
| The hand built token with claims `{"exp":-1}` (header `{"alg":"HS256"}`, the 32 byte signature) is refused at the current time 0 with HS256 allowed. | `Spec.rejects_negative_exp` |
| The same header and signature with claims `{"exp":-0.5}` are accepted at the current time -1. | `Spec.accepts_negative_fraction_exp` |
| The token `eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImF1ZCI6Im90aGVyLXRlbmFudCJ9.AQID`, whose claims are `{"iss":"joe","exp":2000000000,"aud":"other-tenant"}`, parses and is refused when HS256 is allowed, the current time is 1500000000, the issuer must be `joe`, and no audience is expected. | `Spec.rejects_aud_without_audience` |
| The same token is accepted under the same context when the expected audience is `other-tenant`. | `Spec.accepts_aud_with_audience` |

The token theorems rest on the proofs in
`Proofs/Token.lean`. The print of a parsed token is the
received text because the token keeps the first two parts
as received and the strict base64url decoder accepts a
signature part only when it is the canonical encoding of
its bytes (`Jws.Base64url.Proofs.encode_decode`).
`Jws.Proofs.parseToken_print` is a chain of the three
round trips under it, the JSON text round trip
(`Json.Proofs.parse_print`, carried in with the JSON
code), the UTF-8 round trip (`Spec.utf8_decode_encode`),
and the base64url round trip (`Spec.decode_encode`). The
base64url and UTF-8 layers prove both directions, so each
decoder is exactly the inverse of its encoder; the
converse directions (`Spec.encode_decode`,
`Spec.utf8_encode_decode`) are proved in
`Proofs/B64.lean` and `Proofs/Utf8.lean`. The theorems about acceptance are
proved in `Proofs/Check.lean`, and the theorems about the
value of a number in `Proofs/Num.lean`. The single token theorems
are named fixed cases in the test harness, run through
the same `Jws.parseToken` and `Jws.accept` the command
line tool calls. Those with one context are checked in
the kernel with `decide +kernel`; those that hold under
every context combine a kernel-checked computation on the
token with `Jws.Proofs.accept_false_of_shape`, which says
that a token failing the context-free shape rules is
refused under every context.

Every theorem above checks against the standard three
axioms only (`propext`, `Classical.choice`, `Quot.sound`):
`lake comparator --paranoid` allows no other.

The command line tool in `Main.lean` calls
`Jws.parseToken`, `Jws.accept`, and `Jws.printToken`
directly, the same functions the theorems are about. It
answers an accepted token with `Jws.printToken` of the
parsed token, which `Spec.printToken_parse` proves is the
token text it parsed, so the answer's signature still
matches its signing input. That the tool does this is not
a theorem: no statement covers `Main.lean` (see below),
and the tests check it, including the RFC 7515 A.1 HMAC
on the tool's answer.

## What is not proved

- Repeated names inside objects nested in the header or
  the claims: the check does not look for them (see
  below), and no theorem covers them.
- That the checker accepts every token `SPEC.md` says it
  should, beyond the single inputs the theorems above
  pin. `Spec.accept_sound` proves the other direction,
  that an accepted token meets every rule; that a token
  meeting every rule is accepted (completeness) rests on
  the tests: the RFC examples, the mutation cases, and the
  differential corpus against the harness oracle.
- Signature verification, as stated above: nothing about
  keys, signing inputs, or any algorithm. A caller that
  reads claims from this slice without verifying the
  signature has not checked authenticity.
- That the JSON parser turns away every text outside the
  RFC 8259 grammar, and lone surrogate escapes. The json
  slice proves only that the parser reads back what its
  printer writes (`Json.Proofs.parse_print`); its
  rejections rest on the json slice's tests and on the
  malformed JSON cases here.
- That the JSON printer gives back the text it parsed.
  It does not (it writes a canonical form, without the
  whitespace a sender may have used), and the json
  slice proves only the parse-after-print direction.
  The token therefore keeps its received parts, and
  `Spec.parseToken_print` is stated for tokens made from
  values with `Jws.makeToken`.
- That a token value built by hand, not by `parseToken`
  or `makeToken`, has parts and values that match: the
  `Token` structure does not enforce it, and the theorems
  cover only those two ways of making one.
- That the JSON parser hands the checker only number
  texts of the JSON grammar. `Spec.numVal_value` and
  `Spec.numVal_cmp_now` cover every text of the grammar;
  the json slice's parser checks the grammar before it
  builds a number, but no theorem here says so. The tests
  cover it, comparing the date rules with Python's
  `Decimal` on fractions, exponent spellings, and
  exponents of 999999999 and -999999999.
- Reading requests and printing answers in `Main.lean`:
  line splitting, the field format, the decimal code
  reading. The tests cover them, malformed requests
  included.
- Speed. The code works on lists, which suits proofs,
  not large tokens.

Six readings worth naming, all stated in `SPEC.md` and
pinned by tests:

- An empty signature part is well formed base64url, but
  the checker turns it away: RFC 7515 never produces an
  empty signature for a signing algorithm, and the
  algorithm name `none` is turned away outright, together
  with any context whose allowlist names `none`, so the
  none case never reaches acceptance. The theorem
  `Spec.rejects_empty_signature` pins the emptied
  signature on the RFC's own A.1 token.
- A header or claims object that repeats a member name
  is turned away (`SPEC.md` rule 17), whichever copy
  would have passed: RFC 7515 section 4 and RFC 7519
  section 4 allow a reader only that or reading the last
  copy. `Spec.accept_names_unique` proves it for every
  accepted token. Objects nested inside the header or the
  claims are not checked for repeated names, because no
  rule reads a member of a nested object.
- A header with a `crit` member is turned away whatever
  `crit` holds (`SPEC.md` rule 18): this slice
  understands no extension, and RFC 7515 section 4.1.11
  makes a token invalid when `crit` names one the reader
  does not understand. `Spec.accept_no_crit` proves it
  for every accepted token.
- With no expected audience, a token that carries `aud`
  is turned away (`SPEC.md` rule 16): RFC 7519 section
  4.1.3 asks a reader that does not identify itself with
  a value in `aud` to reject the token. PyJWT reads it
  the same way; some other libraries accept such a
  token.
- `exp`, `nbf`, and `iat` may be fractional (RFC 7519
  section 2 lets a NumericDate be a non-integer), and are
  compared exactly with the current time, a whole number
  of seconds (`SPEC.md` rule 9).
- The payload must be JSON (a JWT claims set), so a JWS
  with an arbitrary payload, which RFC 7515 allows, is
  turned away at parse. RFC 7515 Appendix A.4 (ES512,
  payload `Payload`) is such a token; the tests run it as
  a fixed case expecting refusal, and it is left out of
  the cases expected to pass.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions
  into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it
  puts in place of some definitions the proofs reason
  about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 7515 and RFC
  7519 you intend. The proofs are about the parser and checker in
  this repo following the statements exactly; the
  fidelity of the spec to the RFC is a reading, pinned
  in `SPEC.md` where the RFC leaves a choice open.
- The oracle in `tests/run_tests.py`, written from
  `SPEC.md`, and PyJWT and cryptography (pinned in
  `tests/requirements.txt`), which built the tokens and
  gave the probe verdicts in `tests/pyjwt_corpus.json`.
  Both are evidence, not proof. The expected verdicts are
  the oracle's; PyJWT's decodes and its verdicts on the
  probe tokens are compared beside them, and the results
  file names each difference and the versions used.
- The line handling in `Main.lean` (splitting a request
  line, reading the six fields and their decimal codes,
  and the partial IO loop that reads lines until the
  input ends). No statement depends on any of it, and
  the tests drive it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed RFC cases,
   the mutation cases, the malformed request cases, the
   two seeded corpora, and the PyJWT tokens and probe
   verdicts, with counts and any failures written to
   `tests/TEST-RESULTS.md`. The harness reads the PyJWT
   tokens and verdicts from `tests/pyjwt_corpus.json` and
   needs no library beyond Python's own.
3. `lake build`: the libraries, the proofs, and the tool
   build clean.
4. Read `SPEC.md` against RFC 7515 and RFC 7519 and check
   the pinned readings are the ones you want.
