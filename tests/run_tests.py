#!/usr/bin/env python3
"""Test harness for the JWS compact parser and checker.

Three parts, matching the slice plan:

1. Fixed cases: the RFC 7515 Appendix A examples (A.1 HS256,
   A.2 RS256, A.3 ES256, A.5 the unsecured none example; the
   RFC 7519 section 3.1 example token is byte for byte the A.1
   token, so the A.1 cases cover it), each with contexts that
   accept and contexts that reject. The A.1 token with its
   signature part emptied, under an otherwise passing context,
   is a fixed reject case.

2. Differential: tokens built with PyJWT (read from the committed
   corpus tests/pyjwt_corpus.json, which tests/make_pyjwt_corpus.py
   builds from the pinned tests/requirements.txt), plus hand built
   tokens and a seeded random corpus, each run under several check
   contexts. Every verdict (and, on acceptance, the token text the
   tool answers with) is compared against an oracle that
   reimplements SPEC.md in Python. PyJWT also cross checks the
   parsing: its own unverified decode of each token it built, kept
   in the corpus, is compared with the oracle's parse.

3. Mutations and malformed requests: padding added, characters
   outside the alphabet, two or four parts, a header that is not
   an object, alg missing, alg none with an empty signature,
   exp equal to now, nbf equal to now, audience arrays that do
   and do not hold the expected value, a fractional exp, and
   more; plus request lines that must be answered with `error`.

The oracle is the authority for verdicts. PyJWT never decides a
verdict here: it builds well formed tokens and cross checks
decoding, because its own checks differ from this slice's rules
(it verifies signatures and registered claims its own way when
asked, and accepts some framings this slice turns away).

Run: python3 tests/run_tests.py (uses .lake/build/bin/jws; needs
only the Python standard library). Writes tests/TEST-RESULTS.md
with real counts.
"""

import base64
import json
import random
import re
import subprocess
import sys
from decimal import Decimal
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "jws"
SEED = 20261026

# ---------------------------------------------------------------
# The oracle: SPEC.md reimplemented in Python.
# JSON values are tuples mirroring the Lean Json type:
#   ('null',) ('bool', b) ('num', source text) ('str', s)
#   ('arr', [v ...]) ('obj', [(k, v) ...])   pairs in source order
# ---------------------------------------------------------------

ALPHABET = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_")


def b64url_decode_strict(part):
    """Bytes for a base64url part under the strict rules, or None."""
    if any(ch not in ALPHABET for ch in part):
        return None
    if len(part) % 4 == 1:
        return None
    pad = "=" * (-len(part) % 4)
    try:
        raw = base64.urlsafe_b64decode(part + pad)
    except Exception:
        return None
    # Re-encoding must reproduce the part exactly. This is what
    # turns away nonzero unused bits in the final character.
    if base64.urlsafe_b64encode(raw).rstrip(b"=").decode() != part:
        return None
    return raw


def b64url_encode(raw):
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


class BadJson(Exception):
    pass


def _no_constant(x):
    raise BadJson(x)


def _walk_check(v):
    """Reject lone surrogates anywhere, as the Lean parser does."""
    if isinstance(v, tuple):
        tag = v[0]
        if tag == "str":
            if any(0xD800 <= ord(ch) <= 0xDFFF for ch in v[1]):
                raise BadJson("lone surrogate")
        elif tag == "arr":
            for item in v[1]:
                _walk_check(item)
        elif tag == "obj":
            for k, item in v[1]:
                if any(0xD800 <= ord(ch) <= 0xDFFF for ch in k):
                    raise BadJson("lone surrogate in key")
                _walk_check(item)


def json_parse(text):
    """Parse a JSON text into the tuple form, or None."""
    try:
        val = json.loads(
            text,
            object_pairs_hook=lambda pairs: ("obj", list(pairs)),
            parse_int=lambda s: ("num", s),
            parse_float=lambda s: ("num", s),
            parse_constant=_no_constant,
        )
    except Exception:
        return None

    def conv(v):
        if isinstance(v, tuple):
            if v[0] == "obj":
                return ("obj", [(k, conv(x)) for (k, x) in v[1]])
            return v
        if isinstance(v, list):
            return ("arr", [conv(x) for x in v])
        if isinstance(v, str):
            return ("str", v)
        if isinstance(v, bool):
            return ("bool", v)
        if v is None:
            return ("null",)
        raise BadJson("unexpected")

    try:
        out = conv(val)
        _walk_check(out)
    except BadJson:
        return None
    return out


HEX = "0123456789abcdef"


def json_print(v):
    tag = v[0]
    if tag == "null":
        return "null"
    if tag == "bool":
        return "true" if v[1] else "false"
    if tag == "num":
        return v[1]
    if tag == "str":
        out = ['"']
        for ch in v[1]:
            n = ord(ch)
            if ch == '"':
                out.append('\\"')
            elif ch == "\\":
                out.append("\\\\")
            elif n == 8:
                out.append("\\b")
            elif n == 9:
                out.append("\\t")
            elif n == 10:
                out.append("\\n")
            elif n == 12:
                out.append("\\f")
            elif n == 13:
                out.append("\\r")
            elif n < 32:
                out.append("\\u00" + HEX[n // 16] + HEX[n % 16])
            else:
                out.append(ch)
        out.append('"')
        return "".join(out)
    if tag == "arr":
        return "[" + ",".join(json_print(x) for x in v[1]) + "]"
    if tag == "obj":
        return "{" + ",".join(json_print(("str", k)) + ":" + json_print(x)
                              for (k, x) in v[1]) + "}"
    raise BadJson(tag)


def lookup(name, obj):
    """The member of that name. The oracle reads names only from
    objects it has found to repeat no name (names_unique below), as
    the Lean check does, so the copy found is the only copy."""
    if obj[0] != "obj":
        return None
    for (k, v) in obj[1]:
        if k == name:
            return v
    return None


def names_unique(obj):
    """No member name of the object appears twice (SPEC rule 17).
    Names are compared after JSON unescaping, so "\\u0061lg" and
    "alg" are the same name."""
    names = [k for (k, _) in obj[1]]
    return len(set(names)) == len(names)


NUM_RE = re.compile(r"^-?(0|[0-9]+)(\.[0-9]+)?([eE][+-]?[0-9]+)?$")


def date_claim(claims, name):
    """'absent', 'bad', or a Decimal integer value."""
    v = lookup(name, claims)
    if v is None:
        return "absent"
    if v[0] != "num" or not NUM_RE.match(v[1]):
        return "bad"
    d = Decimal(v[1])
    if d != d.to_integral_value():
        return "bad"
    return d


def shape_ok(claims):
    iss = lookup("iss", claims)
    if iss is not None and iss[0] != "str":
        return False
    aud = lookup("aud", claims)
    if aud is not None:
        if aud[0] == "str":
            pass
        elif aud[0] == "arr" and all(x[0] == "str" for x in aud[1]):
            pass
        else:
            return False
    return True


def oracle_check(token_text, now, allow, required, issuer, audience):
    """The canonical reprinted token when accepted, else None.

    now is None for no time comparisons. allow, required are
    lists of names. issuer, audience are strings or None."""
    if "none" in allow:
        return None
    parts = token_text.split(".")
    if len(parts) != 3:
        return None
    raws = [b64url_decode_strict(p) for p in parts]
    if any(r is None for r in raws):
        return None
    if len(raws[2]) == 0:
        # An empty signature part is always turned away (SPEC
        # rule 2): no signing algorithm produces one, and alg
        # none is turned away on its own below.
        return None
    try:
        header_text = raws[0].decode("utf-8")
        claims_text = raws[1].decode("utf-8")
    except UnicodeDecodeError:
        return None
    header = json_parse(header_text)
    claims = json_parse(claims_text)
    if header is None or claims is None:
        return None
    if header[0] != "obj" or claims[0] != "obj":
        return None
    if not names_unique(header) or not names_unique(claims):
        # A repeated member name in either object turns the token
        # away (SPEC rule 17; RFC 7515 section 4, RFC 7519 section 4).
        return None
    if any(k == "crit" for (k, _) in header[1]):
        # The slice understands no extension, so a crit member of
        # any value turns the token away (SPEC rule 18; RFC 7515
        # section 4.1.11).
        return None
    alg = lookup("alg", header)
    if alg is None or alg[0] != "str":
        return None
    if alg[1] == "none" or alg[1] not in allow:
        return None
    for name in required:
        if lookup(name, claims) is None:
            return None
    for name in ("exp", "nbf", "iat"):
        if date_claim(claims, name) == "bad":
            return None
    if now is not None:
        exp = date_claim(claims, "exp")
        if exp not in ("absent", "bad") and not (Decimal(now) < exp):
            return None
        nbf = date_claim(claims, "nbf")
        if nbf not in ("absent", "bad") and (Decimal(now) < nbf):
            return None
    if not shape_ok(claims):
        return None
    if issuer is not None:
        iss = lookup("iss", claims)
        if iss is None or iss[0] != "str" or iss[1] != issuer:
            return None
    if audience is not None:
        aud = lookup("aud", claims)
        if aud is None:
            return None
        if aud[0] == "str":
            if aud[1] != audience:
                return None
        elif aud[0] == "arr":
            if not any(x[0] == "str" and x[1] == audience for x in aud[1]):
                return None
        else:
            return None
    canon = ".".join([
        b64url_encode(json_print(header).encode("utf-8")),
        b64url_encode(json_print(claims).encode("utf-8")),
        b64url_encode(raws[2]),
    ])
    return canon


# ---------------------------------------------------------------
# The Lean side: request encoding and the runner.
# ---------------------------------------------------------------

def codes_of(text):
    return ",".join(str(ord(ch)) for ch in text)


def check_request(token_text, now, allow, required, issuer, audience):
    now_text = "" if now is None else str(now)
    allow_text = ",".join(allow)
    req_text = ",".join(required)
    iss_text = "" if issuer is None else issuer
    aud_text = "" if audience is None else audience
    fields = [token_text, now_text, allow_text, req_text, iss_text, aud_text]
    return "check " + ";".join(codes_of(f) for f in fields)


def run_lean(lines):
    proc = subprocess.run([str(EXE)], input="\n".join(lines) + "\n",
                          capture_output=True, text=True, timeout=1200)
    if proc.returncode != 0:
        raise RuntimeError("lean exe failed: " + proc.stderr[:2000])
    return proc.stdout.splitlines()


def decode_answer(ans):
    """'ok:<codes>' -> token text; 'none' -> None; 'error' -> 'error'."""
    if ans == "none":
        return None
    if ans == "error":
        return "error"
    if ans.startswith("ok:"):
        body = ans[3:]
        if body == "":
            return ""
        return "".join(chr(int(x)) for x in body.split(","))
    raise ValueError("bad answer: " + ans[:80])


# ---------------------------------------------------------------
# Case collection. Each entry: (name, request line, expected)
# where expected is a token text (accepted, canonical), None
# (rejected), or "error" (malformed request).
# ---------------------------------------------------------------

CASES = []


def add_check(name, token, now, allow, required, issuer, audience):
    want = oracle_check(token, now, allow, required, issuer, audience)
    CASES.append((name, check_request(token, now, allow, required, issuer,
                                       audience), want))


def add_raw(name, line, want):
    CASES.append((name, line, want))


# --- RFC 7515 Appendix A -------------------------------------

PAYLOAD_B64 = ("eyJpc3MiOiJqb2UiLA0KICJleHAiOjEzMDA4MTkzODAsDQogImh0dHA6Ly9"
               "leGFtcGxlLmNvbS9pc19yb290Ijp0cnVlfQ")
A1 = ("eyJ0eXAiOiJKV1QiLA0KICJhbGciOiJIUzI1NiJ9." + PAYLOAD_B64 +
      ".dBjftJeZ4CVP-mB92K27uhbUJU1p1r_wW1gFWFOEjXk")
A2 = ("eyJhbGciOiJSUzI1NiJ9." + PAYLOAD_B64 +
      ".cC4hiUPoj9Eetdgtv3hF80EGrhuB__dzERat0XF9g2VtQgr9PJbu3XOiZj5RZmh7AAuH"
      "Im4Bh-0Qc_lF5YKt_O8W2Fp5jujGbds9uJdbF9CUAr7t1dnZcAcQjbKBYNX4BAynRFdiu"
      "B--f_nZLgrnbyTyWzO75vRK5h6xBArLIARNPvkSjtQBMHlb1L07Qe7K0GarZRmB_eSN93"
      "83LcOLn6_dO--xi12jzDwusC-eOkHWEsqtFZESc6BfI7noOPqvhJ1phCnvWh6IeYI2w9Q"
      "OYEUipUTI8np6LbgGY9Fs98rqVt5AXLIhWkWywlVmtVrBp0igcN_IoypGlUPQGe77Rw")
A3 = ("eyJhbGciOiJFUzI1NiJ9." + PAYLOAD_B64 +
      ".DtEhU3ljbEg8L38VWAfUAqOyKAM6-Xx-F4GawxaepmXFCgfTjDxw5djxLa8ISlSApmWQ"
      "xfKTUJqPP3-Kg6NU1Q")
A5 = "eyJhbGciOiJub25lIn0." + PAYLOAD_B64 + "."

add_check("A.1 accept (HS256 allowed, now before exp, issuer joe)",
          A1, 1300819000, ["HS256"], [], "joe", None)
add_check("A.1 reject (alg not allowed)", A1, 1300819000, ["RS256"], [],
          None, None)
add_check("A.1 reject (now equal to exp)", A1, 1300819380, ["HS256"], [],
          None, None)
add_check("A.1 reject (now after exp)", A1, 1400000000, ["HS256"], [],
          None, None)
add_check("A.1 reject (wrong issuer)", A1, 1300819000, ["HS256"], [],
          "bob", None)
add_check("A.1 accept (required claims present)", A1, 1300819000,
          ["HS256"], ["exp", "iss"], None, None)
add_check("A.1 reject (required claim missing)", A1, 1300819000,
          ["HS256"], ["sub"], None, None)
add_check("A.1 accept (no time checks, issuer checked)", A1, None,
          ["HS256"], [], "joe", None)
A1_EMPTY_SIG = A1.rsplit(".", 1)[0] + "."
add_check("A.1 reject (signature part emptied, otherwise passing"
          " context)", A1_EMPTY_SIG, 1300819000, ["HS256"], [],
          "joe", None)
add_check("A.2 accept (RS256 allowed, now before exp, issuer joe)",
          A2, 1300819000, ["RS256"], [], "joe", None)
add_check("A.2 reject (alg not allowed)", A2, 1300819000, ["HS256"], [],
          None, None)
add_check("A.3 accept (ES256 allowed, now before exp)", A3, 1300819000,
          ["ES256"], [], None, None)
add_check("A.3 reject (now equal to exp)", A3, 1300819380, ["ES256"], [],
          None, None)
add_check("A.5 reject (alg none, HS256 allowed)", A5, 1300819000,
          ["HS256"], [], None, None)
add_check("A.5 reject (alg none, allowlist names none)", A5, 1300819000,
          ["none"], [], None, None)
add_check("A.5 reject (alg none, allowlist names none and HS256)",
          A5, 1300819000, ["none", "HS256"], [], None, None)
add_check("HS256 token reject (allowlist names none at all)", A1,
          1300819000, ["none", "HS256"], [], None, None)

# --- Hand built tokens for mutations --------------------------

def hand_token(header_bytes, payload_bytes, sig_bytes):
    return ".".join([b64url_encode(header_bytes),
                     b64url_encode(payload_bytes),
                     b64url_encode(sig_bytes)])


GOOD_H = b'{"alg":"HS256"}'
GOOD_P = b'{"iss":"joe","exp":2000000000}'
SIG = bytes(range(32))
BASE = hand_token(GOOD_H, GOOD_P, SIG)
NOW = 1500000000

add_check("base accept", BASE, NOW, ["HS256"], [], "joe", None)

parts = BASE.split(".")
add_check("mutation: padding on header part",
          parts[0] + "=." + parts[1] + "." + parts[2],
          NOW, ["HS256"], [], None, None)
add_check("mutation: padding on payload part",
          parts[0] + "." + parts[1] + "=." + parts[2],
          NOW, ["HS256"], [], None, None)
add_check("mutation: padding on signature part",
          parts[0] + "." + parts[1] + "." + parts[2] + "=",
          NOW, ["HS256"], [], None, None)
add_check("mutation: plus character in signature",
          parts[0] + "." + parts[1] + "." + parts[2][:-1] + "+",
          NOW, ["HS256"], [], None, None)
add_check("mutation: slash character in payload",
          parts[0] + "." + "/" + parts[1][1:] + "." + parts[2],
          NOW, ["HS256"], [], None, None)
add_check("mutation: star character in header",
          "*" + parts[0][1:] + "." + parts[1] + "." + parts[2],
          NOW, ["HS256"], [], None, None)
add_check("mutation: two parts only", parts[0] + "." + parts[1],
          NOW, ["HS256"], [], None, None)
add_check("mutation: four parts", BASE + ".AAAA",
          NOW, ["HS256"], [], None, None)
add_check("mutation: empty token", "", NOW, ["HS256"], [], None, None)
add_check("mutation: two dots only", "..", NOW, ["HS256"], [], None, None)
add_check("mutation: header part length 1 mod 4",
          "AAAAA." + parts[1] + "." + parts[2],
          NOW, ["HS256"], [], None, None)
add_check("mutation: signature part length 1 mod 4",
          parts[0] + "." + parts[1] + ".AAAAA",
          NOW, ["HS256"], [], None, None)
# signature 'AR': last character value 17, unused bits nonzero in a
# two character (one byte) final group.
add_check("mutation: signature unused bits set",
          parts[0] + "." + parts[1] + ".AR",
          NOW, ["HS256"], [], None, None)
add_check("empty signature part (reject; this case pinned the"
          " earlier reading as an accept, flipped by the"
          " 2026-10-27 review change)",
          parts[0] + "." + parts[1] + ".",
          NOW, ["HS256"], [], "joe", None)
add_check("one byte signature (accepted)",
          hand_token(GOOD_H, GOOD_P, b"\x01"),
          NOW, ["HS256"], [], None, None)

add_check("mutation: header is an array",
          hand_token(b'["HS256"]', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: header is a string",
          hand_token(b'"HS256"', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: payload is a number",
          hand_token(GOOD_H, b'42', SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: payload is not JSON",
          hand_token(GOOD_H, b'{oops', SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: header is not UTF-8",
          hand_token(b'\xff\xfe{"alg":"HS256"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: alg missing",
          hand_token(b'{"typ":"JWT"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: alg not a string",
          hand_token(b'{"alg":256}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("mutation: alg none with a signature present",
          hand_token(b'{"alg":"none"}', GOOD_P, SIG),
          NOW, ["HS256", "none"], [], None, None)
add_check("alg None capital (case differs, accepted when allowed)",
          hand_token(b'{"alg":"None"}', GOOD_P, SIG),
          NOW, ["None"], [], None, None)

def claims_token(claims_bytes, header_bytes=GOOD_H, sig=SIG):
    return hand_token(header_bytes, claims_bytes, sig)

add_check("mutation: exp equal to now (reject)",
          claims_token(b'{"exp":1500000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: exp one second after now (accept)",
          claims_token(b'{"exp":1500000001}'),
          NOW, ["HS256"], [], None, None)
add_check("nbf equal to now (accept)",
          claims_token(b'{"nbf":1500000000,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: nbf one second after now (reject)",
          claims_token(b'{"nbf":1500000001,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: fractional exp (reject)",
          claims_token(b'{"exp":2000000000.5}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: fractional exp with no time checks (reject)",
          claims_token(b'{"exp":2000000000.5}'),
          None, ["HS256"], [], None, None)
add_check("mutation: exp as a string (reject)",
          claims_token(b'{"exp":"2000000000"}'),
          NOW, ["HS256"], [], None, None)
add_check("exp in exponent form, same value (accept)",
          claims_token(b'{"exp":2.0e9}'),
          NOW, ["HS256"], [], None, None)
add_check("exp with scaled exponent (accept)",
          claims_token(b'{"exp":20000000000e-1}'),
          NOW, ["HS256"], [], None, None)
add_check("exp huge exponent text (accept, no bulk)",
          claims_token(b'{"exp":1e999999999}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: negative exp, now zero (reject)",
          claims_token(b'{"exp":-1}'),
          0, ["HS256"], [], None, None)
add_check("negative now before a small exp (accept)",
          claims_token(b'{"exp":100}'),
          -5, ["HS256"], [], None, None)
add_check("mutation: fractional iat (reject)",
          claims_token(b'{"iat":1.5,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("iat whole in exponent form (accept)",
          claims_token(b'{"iat":1.5e9,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: nbf as a boolean (reject)",
          claims_token(b'{"nbf":true,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: iss a number (reject)",
          claims_token(b'{"iss":7,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: aud a number (reject)",
          claims_token(b'{"aud":7,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: aud array with a number inside (reject)",
          claims_token(b'{"aud":["api",7],"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("aud array containing the expected value (accept)",
          claims_token(b'{"aud":["api","web"],"exp":2000000000}'),
          NOW, ["HS256"], [], None, "web")
add_check("mutation: aud array missing the expected value (reject)",
          claims_token(b'{"aud":["api","web"],"exp":2000000000}'),
          NOW, ["HS256"], [], None, "mobile")
add_check("aud string equal to the expected value (accept)",
          claims_token(b'{"aud":"api","exp":2000000000}'),
          NOW, ["HS256"], [], None, "api")
add_check("mutation: expected audience, aud missing (reject)",
          claims_token(b'{"exp":2000000000}'),
          NOW, ["HS256"], [], None, "api")
add_check("mutation: expected issuer, iss missing (reject)",
          claims_token(b'{"exp":2000000000}'),
          NOW, ["HS256"], [], "joe", None)
add_check("required claim of number type still counts as present",
          claims_token(b'{"foo":42,"exp":2000000000}'),
          NOW, ["HS256"], ["foo"], None, None)
# Repeated member names: refused whichever copy a reader would take
# (SPEC rule 17). These cases pinned the old first-copy reading as
# accepts; review 1 item 1 asked for them to be refused.
add_check("duplicate iss (joe then bob): refused, issuer joe",
          claims_token(b'{"iss":"joe","iss":"bob","exp":2000000000}'),
          NOW, ["HS256"], [], "joe", None)
add_check("duplicate iss (joe then bob): refused, issuer bob",
          claims_token(b'{"iss":"joe","iss":"bob","exp":2000000000}'),
          NOW, ["HS256"], [], "bob", None)
add_check("duplicate iss (joe then evil): refused",
          "eyJhbGciOiJIUzI1NiJ9.eyJpc3MiOiJqb2UiLCJleHAiOjIwMDAwMDAwMDAsImlzcyI6"
          "ImV2aWwifQ.AQID",
          NOW, ["HS256"], [], "joe", None)
add_check("duplicate alg (HS256 then none): refused",
          "eyJhbGciOiJIUzI1NiIsImFsZyI6Im5vbmUifQ.eyJleHAiOjIwMDAwMDAwMDB9.AQID",
          NOW, ["HS256"], [], None, None)
add_check("duplicate alg (HS256 then none, longer signature): refused",
          hand_token(b'{"alg":"HS256","alg":"none"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate alg (none then HS256): refused",
          hand_token(b'{"alg":"none","alg":"HS256"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate alg (HS256 then RS256), HS256 allowed: refused",
          hand_token(b'{"alg":"HS256","alg":"RS256"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate alg, same value twice: refused",
          hand_token(b'{"alg":"HS256","alg":"HS256"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate alg spelled with an escape: refused",
          hand_token(b'{"alg":"HS256","\\u0061lg":"none"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate kid in the header: refused",
          hand_token(b'{"alg":"HS256","kid":"a","kid":"b"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("duplicate exp (live then expired): refused",
          claims_token(b'{"exp":2000000000,"exp":1000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("duplicate exp (expired then live): refused",
          claims_token(b'{"exp":1000000000,"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("duplicate aud: refused",
          claims_token(b'{"aud":"api","exp":2000000000,"aud":"web"}'),
          NOW, ["HS256"], [], None, "api")
add_check("duplicate name nobody reads (foo): refused",
          claims_token(b'{"foo":1,"exp":2000000000,"foo":2}'),
          NOW, ["HS256"], [], None, None)
add_check("repeated name inside a nested object, not read: accepted",
          claims_token(b'{"exp":2000000000,"ctx":{"a":1,"a":2}}'),
          NOW, ["HS256"], [], None, None)

# The crit header parameter: any crit member is refused, since the
# slice understands no extension (SPEC rule 18). Review 1 item 2.
add_check("crit naming b64: refused",
          "eyJhbGciOiJIUzI1NiIsImI2NCI6ZmFsc2UsImNyaXQiOlsiYjY0Il19."
          "eyJleHAiOjIwMDAwMDAwMDB9.AQID",
          NOW, ["HS256"], [], None, None)
add_check("crit naming b64, longer signature: refused",
          hand_token(b'{"alg":"HS256","b64":false,"crit":["b64"]}',
                     GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit naming an unknown extension: refused",
          hand_token(b'{"alg":"HS256","crit":["x-unknown"],"x-unknown":1}',
                     GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit naming a URI extension (RFC 7515 E shape): refused",
          hand_token(b'{"alg":"HS256","crit":["http://example.invalid/'
                     b'UNDEFINED"],"http://example.invalid/UNDEFINED":true}',
                     GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit as an empty list: refused",
          hand_token(b'{"alg":"HS256","crit":[]}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit not a list: refused",
          hand_token(b'{"alg":"HS256","crit":"exp"}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit null: refused",
          hand_token(b'{"alg":"HS256","crit":null}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit spelled with an escape: refused",
          hand_token(b'{"alg":"HS256","\\u0063rit":["b64"],"b64":false}',
                     GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("crit as a claim name, not a header name: accepted",
          claims_token(b'{"crit":["b64"],"exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("b64 false without crit (not understood, not critical):"
          " accepted",
          hand_token(b'{"alg":"HS256","b64":false}', GOOD_P, SIG),
          NOW, ["HS256"], [], None, None)
add_check("payload whitespace and key order kept in the reprint",
          claims_token(b'{ "exp" : 2000000000 , "iss" : "joe" }'),
          NOW, ["HS256"], [], "joe", None)

# Unicode handling in strings.
add_check("iss with a raw UTF-8 character (accept)",
          claims_token('{"iss":"jé","exp":2000000000}'.encode("utf-8")),
          NOW, ["HS256"], [], "jé", None)
add_check("iss with an escaped character, same value (accept)",
          claims_token(b'{"iss":"j\\u00e9","exp":2000000000}'),
          NOW, ["HS256"], [], "jé", None)
add_check("iss with a surrogate pair escape (accept)",
          claims_token(b'{"iss":"\\uD83D\\uDE00","exp":2000000000}'),
          NOW, ["HS256"], [], "\U0001F600", None)
add_check("mutation: iss with a lone surrogate escape (reject)",
          claims_token(b'{"iss":"\\uD83D","exp":2000000000}'),
          NOW, ["HS256"], [], None, None)
add_check("mutation: payload with an overlong UTF-8 lead (reject)",
          hand_token(GOOD_H, b'{"iss":"j\xc0\xaf","exp":2000000000}', SIG),
          NOW, ["HS256"], [], None, None)

# --- Malformed requests ---------------------------------------

add_raw("malformed: unknown operation", "peek " + codes_of(BASE), "error")
add_raw("malformed: five fields",
        "check " + ";".join([codes_of(BASE), codes_of("1500000000"),
                             codes_of("HS256"), "", ""]), "error")
add_raw("malformed: seven fields",
        "check " + ";".join([codes_of(BASE), codes_of("1500000000"),
                             codes_of("HS256"), "", "", "", ""]), "error")
add_raw("malformed: a field that is not numbers",
        "check " + ";".join(["1,2,x", "", "", "", "", ""]), "error")
add_raw("malformed: a code above the scalar range",
        "check " + ";".join([codes_of(BASE), "1114112", "", "", "", ""]),
        "error")
add_raw("malformed: a surrogate code in the token field",
        "check " + ";".join(["55296", "", "", "", "", ""]), "error")
add_raw("malformed: now field with letters",
        "check " + ";".join([codes_of(BASE), codes_of("12a3"),
                             codes_of("HS256"), "", "", ""]), "error")
add_raw("malformed: now field over 19 digits",
        "check " + ";".join([codes_of(BASE), codes_of("99999999999999999999"),
                             codes_of("HS256"), "", "", ""]), "error")
add_raw("malformed: empty line", "", "error")
add_raw("malformed: check with no payload", "check", "error")
add_check("now field with a minus sign and digits (read as negative)",
          claims_token(b'{"exp":100,"nbf":-50}'),
          -5, ["HS256"], [], None, None)

# ---------------------------------------------------------------
# PyJWT corpus: tokens PyJWT built, read from the committed
# corpus, contexts varied. Verdicts still come from the oracle.
# PyJWT's decode (signature check off), kept in the corpus, cross
# checks the oracle's parse.
# ---------------------------------------------------------------

PYJWT_INFO = {"present": False, "version": None, "cryptography": None,
              "tokens": 0, "decode_comparisons": 0,
              "decode_agreements": 0, "decode_differences": []}

CORPUS = ROOT / "tests" / "pyjwt_corpus.json"


def build_pyjwt_cases():
    """Read the tokens PyJWT built (tests/pyjwt_corpus.json, made by
    tests/make_pyjwt_corpus.py from tests/requirements.txt). The
    corpus is committed, so every run makes the same inputs whether
    or not PyJWT is installed where the harness runs."""
    data = json.loads(CORPUS.read_text(encoding="utf-8"))
    PYJWT_INFO["present"] = True
    PYJWT_INFO["version"] = data["pyjwt"]
    PYJWT_INFO["cryptography"] = data["cryptography"]
    contexts = [
        ("right alg, inside validity", lambda alg: (1500000000, [alg], [],
                                                     None, None)),
        ("wrong alg", lambda alg: (1500000000, ["HS256"] if alg != "HS256"
                                   else ["RS256"], [], None, None)),
        ("issuer and audience set", lambda alg: (1500000000, [alg], [],
                                                 "joe", "api")),
        ("after the common exp", lambda alg: (2100000000, [alg], [],
                                              None, None)),
        ("no time checks", lambda alg: (None, [alg], [], None, None)),
    ]
    for item in data["tokens"]:
        tok = item["token"]
        PYJWT_INFO["tokens"] += 1
        # Cross check the oracle parse against PyJWT's decode.
        parts = tok.split(".")
        header = json_parse(b64url_decode_strict(parts[0]).decode("utf-8"))
        claims = json_parse(b64url_decode_strict(parts[1]).decode("utf-8"))

        def plain(v):
            if v[0] == "obj":
                return {k: plain(x) for (k, x) in v[1]}
            if v[0] == "arr":
                return [plain(x) for x in v[1]]
            if v[0] == "num":
                d = Decimal(v[1])
                return int(d) if d == d.to_integral_value() else float(d)
            return v[1]

        PYJWT_INFO["decode_comparisons"] += 1
        if plain(header) == item["header"] and plain(claims) == item["claims"]:
            PYJWT_INFO["decode_agreements"] += 1
        else:
            PYJWT_INFO["decode_differences"].append(tok[:40])
        for label, make in contexts:
            now, allow, required, issuer, audience = make(item["alg"])
            if item["alg"] == "none":
                allow = ["none"] if "wrong" not in label else ["HS256"]
            add_check("pyjwt %s token, %s" % (item["alg"], label),
                      tok, now, allow, required, issuer, audience)


# ---------------------------------------------------------------
# Random differential corpus (oracle builds and settles all).
# ---------------------------------------------------------------

def build_random_cases(count=240):
    rng = random.Random(SEED)
    algs = ["HS256", "HS384", "RS256", "ES256", "PS256", "EdDSA", "none",
            "None", "hs256"]
    issuers = ["joe", "issuer.example", "jé", "api-issuer"]
    auds = ["api", "web", "mobile"]

    def rand_claims():
        claims = {}
        if rng.random() < 0.8:
            claims["iss"] = rng.choice(issuers)
        if rng.random() < 0.8:
            claims["exp"] = rng.choice(
                [1400000000, 1500000000, 1600000000, 2000000000, 9999999999])
        if rng.random() < 0.4:
            claims["nbf"] = rng.choice([1400000000, 1500000000, 1600000000])
        if rng.random() < 0.4:
            claims["iat"] = rng.choice([1400000000, 1500000000])
        if rng.random() < 0.6:
            claims["aud"] = (rng.choice(auds) if rng.random() < 0.5
                             else rng.sample(auds, rng.randint(1, 3)))
        if rng.random() < 0.3:
            claims["sub"] = "user-%d" % rng.randint(1, 99)
        return claims

    for i in range(count):
        alg = rng.choice(algs)
        header = {"alg": alg}
        if rng.random() < 0.4:
            header["typ"] = "JWT"
        if rng.random() < 0.2:
            header["kid"] = "key-%d" % rng.randint(1, 5)
        claims = rand_claims()
        sig = bytes(rng.randrange(256) for _ in range(rng.choice(
            [0, 1, 16, 32, 64])))
        tok = hand_token(
            json.dumps(header, separators=(",", ":")).encode("utf-8"),
            json.dumps(claims, separators=(",", ":"),
                       ensure_ascii=False).encode("utf-8"),
            sig)
        now = rng.choice([None, 1450000000, 1500000000, 1550000000,
                          1700000000, 2100000000])
        allow = rng.sample(algs, rng.randint(1, 3))
        required = rng.sample(["iss", "exp", "aud", "sub", "nbf"],
                              rng.randint(0, 2))
        issuer = rng.choice([None, "joe", "issuer.example", "bob"])
        audience = rng.choice([None, "api", "web", "desktop"])
        add_check("random %d (alg %s)" % (i, alg), tok, now, allow,
                  required, issuer, audience)


# ---------------------------------------------------------------
# Run everything and write the record.
# ---------------------------------------------------------------

def main():
    if not EXE.exists():
        print("executable missing; run lake build first", file=sys.stderr)
        return 1
    build_pyjwt_cases()
    build_random_cases()
    lines = [req for (_, req, _) in CASES]
    answers = run_lean(lines)
    if len(answers) != len(CASES):
        print("answer count mismatch: %d vs %d" % (len(answers), len(CASES)),
              file=sys.stderr)
        return 1
    failures = []
    accepted = 0
    rejected = 0
    errors = 0
    for (name, _, want), ans in zip(CASES, answers):
        try:
            got = decode_answer(ans)
        except ValueError:
            failures.append((name, "unreadable answer " + ans[:60], want))
            continue
        if want == "error":
            errors += 1
            ok = got == "error"
        elif want is None:
            rejected += 1
            ok = got is None
        else:
            accepted += 1
            ok = got == want
        if not ok:
            failures.append((name, got, want))

    fixed = [c for c in CASES if c[0].startswith("A.")]
    fixed_fail = [f for f in failures if f[0].startswith("A.")]

    lines_out = []
    lines_out.append("# Test results: JWS compact parser and checker")
    lines_out.append("")
    lines_out.append("Written by `python3 tests/run_tests.py`, which drives"
                     " the built tool `.lake/build/bin/jws`. A fresh run"
                     " gives the same inputs, seed, and verdicts.")
    lines_out.append("")
    lines_out.append("- Oracle: the SPEC.md rules reimplemented in"
                     " tests/run_tests.py (Python %d.%d), with tokens"
                     " and decodes from PyJWT %s (cryptography %s)"
                     % (sys.version_info[0], sys.version_info[1],
                        PYJWT_INFO["version"], PYJWT_INFO["cryptography"]))
    lines_out.append("- Seed: %d" % SEED)
    lines_out.append("- Inputs: %d" % len(CASES))
    lines_out.append("- Failures: %d" % len(failures))
    lines_out.append("")
    lines_out.append("## The oracle and PyJWT")
    lines_out.append("")
    lines_out.append("Verdicts come from the oracle, which reimplements"
                     " the SPEC.md rules in Python. PyJWT %s built %d"
                     " tokens (HS256, RS256, ES256, and none algorithms),"
                     " kept in tests/pyjwt_corpus.json with PyJWT's own"
                     " unverified decode of each. The harness reads that"
                     " file, so it needs no PyJWT to run; to rebuild the"
                     " corpus, make a virtual environment from"
                     " tests/requirements.txt and run"
                     " tests/make_pyjwt_corpus.py (README, How to run"
                     " it)." % (PYJWT_INFO["version"], PYJWT_INFO["tokens"]))
    lines_out.append("PyJWT's decode was compared with the oracle's"
                     " parse on %d tokens: %d agreements, %d differences."
                     % (PYJWT_INFO["decode_comparisons"],
                        PYJWT_INFO["decode_agreements"],
                        len(PYJWT_INFO["decode_differences"])))
    lines_out.append("")
    lines_out.append("## Counts")
    lines_out.append("")
    lines_out.append("- Total check and request inputs: %d" % len(CASES))
    lines_out.append("- Agreements with the oracle: %d"
                     % (len(CASES) - len(failures)))
    lines_out.append("- Of the verdict cases: %d accepted, %d rejected,"
                     " %d malformed requests answered error"
                     % (accepted, rejected, errors))
    lines_out.append("")
    lines_out.append("## RFC 7515 fixed cases")
    lines_out.append("")
    lines_out.append("The A.5 example is the RFC's unsecured (alg none)"
                     " compact example; in the final RFC text A.6 and A.7"
                     " are JSON Serialization examples, not compact"
                     " tokens, so the none cases use A.5. The RFC 7519"
                     " section 3.1 example token is byte for byte the"
                     " A.1 token, so it is covered by the A.1 cases.")
    lines_out.append("")
    for (name, _, _) in fixed:
        mark = "FAIL" if any(f[0] == name for f in fixed_fail) else "ok"
        lines_out.append("- [%s] %s" % (mark, name))
    lines_out.append("")
    lines_out.append("## Named differences and pinned readings")
    lines_out.append("")
    lines_out.append("- Named change from the 2026-10-27 review: an"
                     " empty signature part is now always turned away"
                     " (SPEC rule 2). RFC 7515 never produces an empty"
                     " signature for a signing algorithm, and alg none"
                     " is turned away on its own, so the none case"
                     " never reaches acceptance. The earlier reading"
                     " accepted an empty signature part for a signing"
                     " algorithm. The fixed case that pinned that"
                     " reading now expects rejection, a new fixed case"
                     " empties the A.1 token's signature part under an"
                     " otherwise passing context and expects rejection,"
                     " and generated corpus tokens with empty signature"
                     " parts follow the same new rule in the oracle.")
    lines_out.append("- Named change from review 1 item 1: a header or"
                     " claims object that repeats a member name is"
                     " turned away (SPEC rule 17; RFC 7515 section 4 and"
                     " RFC 7519 section 4 allow only that or reading the"
                     " last copy). The earlier reading took the first"
                     " copy; the fixed cases that pinned it (duplicate"
                     " iss, duplicate alg) now expect refusal, and new"
                     " cases cover duplicate exp, aud, kid, a name that"
                     " is never read, and a name spelled with a JSON"
                     " escape. Names inside nested objects are not"
                     " checked, since the slice reads no member of a"
                     " nested object; a fixed case pins that.")
    lines_out.append("- Named change from review 1 item 2: a header with"
                     " a `crit` member, of any value, is turned away"
                     " (SPEC rule 18). The slice understands no"
                     " extension, and RFC 7515 section 4.1.11 makes a"
                     " token invalid when `crit` names one the reader"
                     " does not understand. Fixed cases cover b64, an"
                     " unknown name, a URI name, an empty list, a"
                     " string, null, and an escaped spelling; `crit` as"
                     " a claim name is not a header member and passes.")
    lines_out.append("- The none rule is the exact name `none`. An alg of"
                     " `None` is a different name and can be allowed.")
    lines_out.append("- Date claims are judged by value, not by spelling:"
                     " `2.0e9` and `20000000000e-1` are the whole number"
                     " 2000000000, and `1e999999999` compares without"
                     " ever being written out.")
    lines_out.append("- PyJWT decode differences (its parser against the"
                     " oracle's on well formed tokens): %d."
                     % len(PYJWT_INFO["decode_differences"]))
    if failures:
        lines_out.append("")
        lines_out.append("## Failures")
        lines_out.append("")
        for (name, got, want) in failures:
            lines_out.append("- %s: got %r, wanted %r" % (name, got, want))
    lines_out.append("")
    text = "\n".join(lines_out)
    (ROOT / "tests" / "TEST-RESULTS.md").write_text(text + "\n")
    print("cases: %d, agreements: %d, failures: %d"
          % (len(CASES), len(CASES) - len(failures), len(failures)))
    print("accepted: %d, rejected: %d, error answers: %d"
          % (accepted, rejected, errors))
    print("pyjwt present: %s, decode comparisons: %d, agreements: %d"
          % (PYJWT_INFO["present"], PYJWT_INFO["decode_comparisons"],
             PYJWT_INFO["decode_agreements"]))
    for f in failures[:20]:
        print("FAIL:", f)
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
