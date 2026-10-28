# JWT in the JWS compact form: parser and claims checker — specification

This is the first slice of the jws repo: parse a JSON Web Token
(RFC 7519) in the JWS compact form (RFC 7515 section 5.2), run a
set of shape and claims checks on it, and give the received
token back unchanged. The payload must be a JSON object, a JWT
claims set. RFC 7515 lets a JWS carry any payload bytes; this
slice reads JWTs only, so a JWS whose payload is not JSON does
not parse. RFC 7515 Appendix A.4 (ES512, payload `Payload`) is
such a token, and is left out of the examples this slice
accepts.

**This slice does not verify the signature.** A token that
passes every check below is well formed and its claims are
consistent with the check context. It is not thereby verified:
nothing here shows the signature was made by the holder of any
key, or that it covers these header and payload bytes at all.
Signature verification is the second slice and is out of scope
here. Do not treat a passing answer from this code as a verified
token.

The algorithm allowlist does not stop key and algorithm
confusion (an RSA public key used as an HMAC secret, for
example). A caller's signature checker must use each key with
exactly one algorithm (RFC 8725 section 3.1), and an allowlist
should name algorithms of one family only, not HMAC and public
key algorithms together.

## Framing

A compact token is three base64url parts joined by dots:

```
part1 "." part2 "." part3
```

- Part 1 is the header: UTF-8 JSON text, encoded in base64url.
- Part 2 is the payload, the claims set: UTF-8 JSON text,
  encoded in base64url. (RFC 7515 allows any bytes here; a JWT
  payload is a JSON claims set, and this slice reads JWTs.)
- Part 3 is the signature: raw bytes, encoded in base64url.

Exactly three parts. Two parts or four parts are turned away.
An empty part is allowed by the framing (the empty text is
well formed base64url for zero bytes); the checks below decide
whether what it decodes to is acceptable. In particular an
empty signature part is well formed base64url, and rule 2
below turns it away at the check.

## Base64url, strict

Decoding follows RFC 4648 section 5 with no padding, and is
strict:

- The alphabet is `A-Z a-z 0-9 - _`. Any other character turns
  the part away, including `=` (padding is not part of the
  compact form, so a padded part is turned away) and the
  standard base64 characters `+` and `/`.
- A part whose length is 1 mod 4 is impossible and is turned
  away.
- The unused bits in the final character must be zero. In a
  final group of two characters (one byte), the second
  character's low four bits are unused and must be zero. In a
  final group of three characters (two bytes), the third
  character's low two bits must be zero.

Encoding writes no padding and always sets the unused bits to
zero, so decoding an encoding and encoding a decoding are both
the identity. Both directions are proved in this repo.

The header and payload bytes must then be UTF-8, read strictly:
overlong forms, encodings of the surrogate values U+D800 to
U+DFFF, values above U+10FFFF, stray continuation bytes, and
truncated sequences are all turned away. The texts must then
parse as JSON under the rules of the json slice carried into
this repo (RFC 8259 grammar; lone surrogate escapes in strings
are turned away, as that slice's parser cannot hold them).

## The check

The caller supplies a context:

- an allowlist of algorithm names;
- the current time in seconds, an integer, or no time (see
  below);
- a list of required claim names;
- an expected issuer, or none;
- an expected audience, or none.

The token is accepted only when every rule holds:

1. The framing is exactly three parts, each strict base64url
   (above). The signature bytes are returned unchanged; their
   content is not examined beyond the emptiness rule below.
2. An empty signature part is always turned away. RFC 7515
   never produces an empty signature for a signing algorithm,
   and the one algorithm that uses no signature, `none`, is
   itself turned away by rule 6, so the none case never
   reaches acceptance.
3. The header decodes to a JSON object.
4. The payload decodes to a JSON object (the claims set).
5. The header carries `alg`, and its value is a string.
6. `alg` is not `none`. This holds whatever the allowlist says.
   As a companion rule, an allowlist that itself names `none`
   is an error at the check level: such a context rejects every
   token. (Asking to allow `none` is asking for unsecured
   tokens; this slice does not accept them under any context.)
7. `alg` is on the allowlist. Names are compared exactly,
   character for character: `None` and `hs256` are different
   names from `none` and `HS256`.
8. Every required claim is present in the claims set. Presence
   is all this rule asks; the value's type does not matter for
   this rule.
9. When `exp`, `nbf`, or `iat` is present, its value must be a
   JSON number. A non-number turns the token away. This type
   rule holds even when no current time is supplied. The value
   need not be a whole number: RFC 7519 section 2 lets a
   NumericDate be a non-integer, so `2000000000.5` is half a
   second after 2000000000. The value is judged as an exact
   decimal, not by its spelling: `2.0e9` is 2000000000, and a
   value like `1e999999999` or `1e-999999999` is compared
   exactly, without ever being written out in full.
10. When `exp` is present and a current time is supplied, the
    current time must be before `exp`. A current time equal to
    `exp` rejects (the token is expired at that second).
11. When `nbf` is present and a current time is supplied, the
    current time must be at or after `nbf`. A current time
    equal to `nbf` accepts.
12. `iat` carries no comparison rule in this slice; only the
    type rule (rule 9) applies to it.
13. When `iss` is present, its value must be a string.
14. When `aud` is present, its value must be a string or an
    array of strings (every member a string).
15. When an expected issuer is given, `iss` must be present
    and exactly equal to it. A missing `iss` rejects.
16. When an expected audience is given, `aud` must be that
    string, or an array holding that string as a member. A
    missing `aud` rejects. When no expected audience is given,
    a token that carries `aud` at all is turned away: RFC 7519
    section 4.1.3 asks a reader that does not identify itself
    with a value in `aud` to reject the token, and a caller
    that gives no audience identifies itself with none.
17. Neither the header object nor the claims object repeats a
    member name. Names are compared after JSON unescaping, so
    `"alg"` and `"\u0061lg"` are the same name. RFC 7515 section 4
    (and step 4 of section 5.2) lets a reader either turn away a
    header that repeats a parameter name or use only the last
    copy, and RFC 7519 section 4 says the same for claim names;
    this slice turns the token away, whatever the repeated name
    and whichever copy would have passed. Members of objects
    nested inside the header or the claims (for example the
    value of a private claim that is itself an object) are not
    checked for repeats: no rule reads a member of a nested
    object.
18. The header has no `crit` member, whatever its value (a list
    of names, an empty list, or anything else). `crit` lists the
    extensions a reader must understand, and RFC 7515 section
    4.1.11 makes the JWS invalid when it names one the reader
    does not. This slice understands no extension, so every
    `crit` header is turned away. That includes RFC 7797's
    `"b64":false`, which changes what the signature covers.
    Other header parameters besides `alg` (`typ`, `kid`, `b64`
    without `crit`, and any other) are not read, as RFC 7515
    section 4 asks for parameters a reader does not understand.

When no current time is supplied, rules 10 and 11 are skipped;
every other rule, including the type rule 9, still applies.

Names are read from objects with the JSON code's lookup. By
rule 17 an accepted token's two objects hold each name at most
once, so the copy read is the only copy. The parser itself keeps
every pair as written; only the check turns repeats away.

## Model and printing

A token value holds the first two parts exactly as received
(the header part and the payload part, base64url text), the
header JSON value and the claims JSON value they decode to, and
the signature bytes. Keeping the two parts matters: with the dot
between them they are the JWS Signing Input of RFC 7515 section
5.2 step 8, which a signature verifier needs byte for byte, and
the JSON printer below does not give back the text it parsed
(it drops whitespace, for one; RFC 7515 A.1's header has a CR LF
and a space in it).

Printing a token writes the two held parts, then the signature
bytes in base64url without padding, joined by dots. For a parsed
token this gives back the received text, byte for byte
(`Spec.printToken_parse`): the parser keeps the first two parts,
and the strict base64url decoder accepts a signature part only
when it is the canonical encoding of its bytes. What the parser
reads is stated too (`Spec.parseToken_reads`): the text splits at
its dots into exactly those three parts, and the header and
claims values are what the two held parts decode to through
strict base64url, strict UTF-8, and the JSON parser.

A token can also be made from values (`Jws.makeToken`): each JSON
part is written with the json slice's canonical printer (no
spaces, object pairs in the order held, numbers kept as their
source text, strings escaped in that printer's fixed way),
encoded as UTF-8, and base64url-encoded without padding. For
values that are well formed in the json slice's sense (its `WF`),
parsing the printed form of such a token gives the same token back
(`Spec.parseToken_print`). Under it, the base64url round trips
(both directions, for arbitrary bytes and for every text the
decoder accepts) and the UTF-8 decode-after-encode round trip are
proved, and the json slice's own parse-after-print theorem is
carried in with its code. The json slice proves no
print-after-parse direction, and none holds, which is why the
token keeps the received parts.

## The command line front end

One request per line on stdin, one answer per line on stdout.
A request is a word, a space, and a payload. The payload is
decimal character codes separated by commas. The one operation
is `check`:

```
check <field1>;<field2>;<field3>;<field4>;<field5>;<field6>
```

The six fields are separated by semicolons (code 59). Each
field is a text written as character codes, in the same comma
separated decimal form as the payload:

- Field 1: the token text.
- Field 2: the current time as decimal digits, with an optional
  leading minus sign, at most 19 digits. Empty means no current
  time (rules 10 and 11 skipped).
- Field 3: the allowlist. The field text is the algorithm names
  joined by commas inside the text itself, for example the text
  `HS256,HS384`. Empty means no algorithms are allowed.
- Field 4: the required claims, in the same comma joined style.
  Empty means no claims are required.
- Field 5: the expected issuer. Empty means none.
- Field 6: the expected audience. Empty means none.

The answer is `ok:` followed by the character codes of the
token text as received (the print of the parsed token, proved
equal to the input) when the token is accepted, `none`
when it is not accepted, and `error` when the request itself
is malformed (wrong field count, a field that is not a code
list, a code that is not a Unicode scalar value, a current
time field that is not an optional minus sign plus at most 19
digits, an unknown operation).

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The single token
theorems are single inputs, one for each named fixed case
in the test harness, run through the same `Jws.parseToken`
and `Jws.accept` the command line tool calls; the tests in
`tests/` cover each rule on many more inputs.
`Spec.accept_sound` covers every token and every context in
the one direction: what acceptance implies. That every token
meeting the rules is accepted is shown only by the single
input theorems and the tests.

| Property | Theorem |
|----------|---------|
| Printing a parsed token gives the received text back, byte for byte | `Spec.printToken_parse` |
| A parsed token holds the received first two parts, the values they decode to, and the signature bytes whose base64url is the third part | `Spec.parseToken_reads` |
| Parsing the printed form of a token made from well formed JSON values gives that token back | `Spec.parseToken_print` |
| Decoding a base64url encoding gives the bytes back | `Spec.decode_encode` |
| The RFC 7515 A.1 token is accepted under its allowlist with no time checks and the issuer checked | `Spec.accepts_rfc_a1` |
| The harness's hand built token is accepted under its base context | `Spec.accepts_hand_built` |
| The RFC 7515 A.5 unsecured token is refused under an HS256 allowlist | `Spec.rejects_unsecured_none` |
| The A.5 token is refused when the allowlist names `none` | `Spec.rejects_unsecured_none_when_allowlist_names_none` |
| The A.5 token is refused when the allowlist names `none` alongside HS256 | `Spec.rejects_unsecured_none_when_allowlist_mixes_none` |
| A token with an empty signature part is refused (rule 2) | `Spec.rejects_empty_signature` |
| A token whose algorithm is outside the allowlist is refused (rule 7) | `Spec.rejects_alg_outside_allowlist` |
| A token with a part that is not strict base64url does not parse | `Spec.rejects_part_not_base64url` |
| A token whose header is not a JSON object is refused (rule 3) | `Spec.rejects_header_not_object` |
| An accepted token meets rules 2 to 18, the date comparisons as `Jws.NumVal.cmp` makes them | `Spec.accept_sound` |
| An accepted token's header and claims are objects that repeat no member name (rules 3, 4, 17) | `Spec.accept_names_unique` |
| The token with header `{"alg":"HS256","alg":"none"}` parses and is refused under every context (rule 17) | `Spec.rejects_duplicate_alg` |
| The token with claims `{"iss":"joe","exp":2000000000,"iss":"evil"}` parses and is refused under every context (rule 17) | `Spec.rejects_duplicate_iss` |
| A token with `exp` 2000000000.5 is accepted at 2000000000 (rules 9, 10) | `Spec.accepts_fractional_exp_before` |
| The same token is refused at 2000000001 (rules 9, 10) | `Spec.rejects_fractional_exp_after` |
| A token carrying `aud` is refused when no audience is expected (rule 16) | `Spec.rejects_aud_without_audience` |
| The same token is accepted when its audience is the expected one | `Spec.accepts_aud_with_audience` |
| An accepted token's header has no `crit` member (rule 18) | `Spec.accept_no_crit` |
| The token with header `{"alg":"HS256","b64":false,"crit":["b64"]}` parses and is refused under every context (rule 18) | `Spec.rejects_crit_b64` |
