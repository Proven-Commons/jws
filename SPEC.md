# JWS compact form: parser and checker — specification

This is the first slice of the jws repo: parse a JWS in compact
form (RFC 7515 section 5.2), run a set of shape and claims
checks on it, and print it back in a canonical form.

**This slice does not verify the signature.** A token that
passes every check below is well formed and its claims are
consistent with the check context. It is not thereby verified:
nothing here shows the signature was made by the holder of any
key, or that it covers these header and payload bytes at all.
Signature verification is the second slice and is out of scope
here. Do not treat a passing answer from this code as a verified
token.

## Framing

A compact token is three base64url parts joined by dots:

```
part1 "." part2 "." part3
```

- Part 1 is the header: UTF-8 JSON text, encoded in base64url.
- Part 2 is the payload, the claims set: UTF-8 JSON text,
  encoded in base64url.
- Part 3 is the signature: raw bytes, encoded in base64url.

Exactly three parts. Two parts or four parts are turned away.
An empty part is allowed by the framing (the empty text is
well formed base64url for zero bytes); the checks below decide
whether what it decodes to is acceptable. In particular an
empty signature part is well formed.

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
   content is not examined.
2. The header decodes to a JSON object.
3. The payload decodes to a JSON object (the claims set).
4. The header carries `alg`, and its value is a string.
5. `alg` is not `none`. This holds whatever the allowlist says.
   As a companion rule, an allowlist that itself names `none`
   is an error at the check level: such a context rejects every
   token. (Asking to allow `none` is asking for unsecured
   tokens; this slice does not accept them under any context.)
6. `alg` is on the allowlist. Names are compared exactly,
   character for character: `None` and `hs256` are different
   names from `none` and `HS256`.
7. Every required claim is present in the claims set. Presence
   is all this rule asks; the value's type does not matter for
   this rule.
8. When `exp`, `nbf`, or `iat` is present, its value must be a
   JSON number whose value is a whole number of seconds. A
   non-number, or a number with a fractional part (for example
   `2000000000.5`), turns the token away. This type rule holds
   even when no current time is supplied. The value is judged
   as an exact decimal, not by its spelling: `2.0e9` is the
   whole number 2000000000, and a value like `1e999999999` is
   compared exactly, without ever being written out in full.
9. When `exp` is present and a current time is supplied, the
   current time must be before `exp`. A current time equal to
   `exp` rejects (the token is expired at that second).
10. When `nbf` is present and a current time is supplied, the
    current time must be at or after `nbf`. A current time
    equal to `nbf` accepts.
11. `iat` carries no comparison rule in this slice; only the
    type rule (rule 8) applies to it.
12. When `iss` is present, its value must be a string.
13. When `aud` is present, its value must be a string or an
    array of strings (every member a string).
14. When an expected issuer is given, `iss` must be present
    and exactly equal to it. A missing `iss` rejects.
15. When an expected audience is given, `aud` must be that
    string, or an array holding that string as a member. A
    missing `aud` rejects.

When no current time is supplied, rules 9 and 10 are skipped;
every other rule, including the type rule 8, still applies.

Names are read from objects with the JSON code's lookup: when a
name appears more than once in an object, the first copy is the
one read.

## Model and printing

A token value holds the header JSON value, the claims JSON
value, and the signature bytes. Printing a token prints each
JSON part with the json slice's canonical printer (no spaces,
object pairs in the order held, numbers kept as their source
text, strings escaped in that printer's fixed way), encodes the
text as UTF-8, base64url-encodes without padding, and joins the
three parts with dots, the signature last.

The main claim, proved in this repo: for a token whose JSON
parts are well formed in the json slice's sense (its `WF`),
parsing the printed token gives the token back
(`Jws.Proofs.parseToken_print`). Under it, the base64url round
trips (both directions, for arbitrary bytes and for every text
the decoder accepts) and the UTF-8 decode-after-encode round
trip are also proved, and the json slice's own parse-after-print
theorem is carried in with its code.

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
  time (rules 9 and 10 skipped).
- Field 3: the allowlist. The field text is the algorithm names
  joined by commas inside the text itself, for example the text
  `HS256,RS256`. Empty means no algorithms are allowed.
- Field 4: the required claims, in the same comma joined style.
  Empty means no claims are required.
- Field 5: the expected issuer. Empty means none.
- Field 6: the expected audience. Empty means none.

The answer is `ok:` followed by the character codes of the
canonical reprinted token when the token is accepted, `none`
when it is not accepted, and `error` when the request itself
is malformed (wrong field count, a field that is not a code
list, a code that is not a Unicode scalar value, a current
time field that is not an optional minus sign plus at most 19
digits, an unknown operation).
