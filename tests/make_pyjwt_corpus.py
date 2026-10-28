#!/usr/bin/env python3
"""Build tests/pyjwt_corpus.json with PyJWT.

The test harness (tests/run_tests.py) reads the tokens this script
writes, so every run of the harness, with or without PyJWT
installed, runs the same inputs. Rerun this script only to rebuild
the corpus, in a virtual environment made from the pinned
requirements:

    python3 -m venv venv
    venv/bin/pip install -r tests/requirements.txt
    venv/bin/python tests/make_pyjwt_corpus.py

The corpus holds two lists.

- "tokens": for each token PyJWT built, the algorithm, the token
  text, and PyJWT's own unverified decode of the header and the
  claims. The RS256 and ES256 keys are made fresh on each rebuild,
  so their signatures differ between rebuilds; nothing in the
  harness depends on signature bytes beyond their being present.
- "probes": HS256 tokens built here byte by byte (so a header can
  repeat a name or carry crit) and signed with PROBE_KEY, each with
  a check context and PyJWT's verdict on it: jwt.decode with that
  key, the context's algorithms, issuer, audience and required
  claims, at the time recorded in "probe_now". The harness runs the
  same token and context, with the current time set to "probe_now",
  and every verdict that differs from PyJWT's must be a named
  difference with its reason.
"""

import base64
import hashlib
import hmac
import json
import sys
import time
from pathlib import Path

import cryptography
import jwt
from cryptography.hazmat.primitives.asymmetric import ec, rsa

OUT = Path(__file__).resolve().parent / "pyjwt_corpus.json"

# The HMAC key for the probes: 32 bytes, so PyJWT raises no key
# length warning.
PROBE_KEY = "jws-slice-probe-key-0123456789ab"

FAR = 2000000000  # an expiry well after any probe_now
PAST = 1400000000  # a not-before well before any probe_now

# (name, header JSON text, claims JSON text, signature kind, context)
# The signature kind is "hmac" (a correct HS256 signature over the
# parts as written) or "empty". The context gives allow, issuer,
# audience and required, as the harness's check context does.
BASE_CTX = {"allow": ["HS256"], "issuer": None, "audience": None,
            "required": []}
PROBES = [
    ("plain", '{"alg":"HS256","typ":"JWT"}',
     '{"iss":"joe","exp":%d}' % FAR, "hmac", BASE_CTX),
    ("CR LF and spaces in both parts, as in A.1",
     '{"typ":"JWT",\r\n "alg":"HS256"}',
     '{"iss":"joe",\r\n "exp":%d,\r\n "nbf":%d}' % (FAR, PAST), "hmac",
     dict(BASE_CTX, issuer="joe")),
    ("escaped characters in names and values",
     '{"\\u0061lg":"HS256"}',
     '{"\\u0069ss":"j\\u00e9","exp":%d}' % FAR, "hmac",
     dict(BASE_CTX, issuer="j\u00e9")),
    ("duplicate alg, HS256 then none", '{"alg":"HS256","alg":"none"}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("duplicate alg, none then HS256", '{"alg":"none","alg":"HS256"}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("duplicate alg spelled with an escape",
     '{"alg":"none","\\u0061lg":"HS256"}', '{"exp":%d}' % FAR, "hmac",
     BASE_CTX),
    ("duplicate iss, joe then evil, issuer evil", '{"alg":"HS256"}',
     '{"iss":"joe","exp":%d,"iss":"evil"}' % FAR, "hmac",
     dict(BASE_CTX, issuer="evil")),
    ("duplicate exp, expired then live", '{"alg":"HS256"}',
     '{"exp":1000000000,"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("duplicate name nobody reads", '{"alg":"HS256"}',
     '{"foo":1,"exp":%d,"foo":2}' % FAR, "hmac", BASE_CTX),
    ("crit naming b64", '{"alg":"HS256","b64":false,"crit":["b64"]}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("crit naming an unknown extension",
     '{"alg":"HS256","crit":["x-unknown"],"x-unknown":1}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("crit an empty list", '{"alg":"HS256","crit":[]}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("crit not a list", '{"alg":"HS256","crit":"exp"}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("b64 false without crit", '{"alg":"HS256","b64":false}',
     '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("fractional exp", '{"alg":"HS256"}', '{"exp":%d.5}' % FAR, "hmac",
     BASE_CTX),
    ("fractional iat and nbf", '{"alg":"HS256"}',
     '{"exp":%d,"iat":%d.25,"nbf":%d.75}' % (FAR, PAST, PAST), "hmac",
     BASE_CTX),
    ("exp in exponent form", '{"alg":"HS256"}', '{"exp":2.0e9}', "hmac",
     BASE_CTX),
    ("expired", '{"alg":"HS256"}', '{"exp":%d}' % PAST, "hmac", BASE_CTX),
    ("not yet valid", '{"alg":"HS256"}',
     '{"exp":%d,"nbf":%d}' % (FAR, FAR - 1), "hmac", BASE_CTX),
    ("iat in the future", '{"alg":"HS256"}',
     '{"exp":%d,"iat":%d}' % (FAR, FAR - 1), "hmac", BASE_CTX),
    ("exp a string", '{"alg":"HS256"}', '{"exp":"%d"}' % FAR, "hmac",
     BASE_CTX),
    ("aud present, no audience expected", '{"alg":"HS256"}',
     '{"exp":%d,"aud":"other-tenant"}' % FAR, "hmac", BASE_CTX),
    ("aud present, the same audience expected", '{"alg":"HS256"}',
     '{"exp":%d,"aud":"other-tenant"}' % FAR, "hmac",
     dict(BASE_CTX, audience="other-tenant")),
    ("aud array holding the expected audience", '{"alg":"HS256"}',
     '{"exp":%d,"aud":["api","web"]}' % FAR, "hmac",
     dict(BASE_CTX, audience="web")),
    ("aud array without the expected audience", '{"alg":"HS256"}',
     '{"exp":%d,"aud":["api","web"]}' % FAR, "hmac",
     dict(BASE_CTX, audience="mobile")),
    ("issuer expected, iss missing", '{"alg":"HS256"}',
     '{"exp":%d}' % FAR, "hmac", dict(BASE_CTX, issuer="joe")),
    ("issuer expected, iss wrong", '{"alg":"HS256"}',
     '{"iss":"bob","exp":%d}' % FAR, "hmac", dict(BASE_CTX, issuer="joe")),
    ("required claim missing", '{"alg":"HS256"}', '{"exp":%d}' % FAR,
     "hmac", dict(BASE_CTX, required=["sub"])),
    ("required claim present", '{"alg":"HS256"}',
     '{"exp":%d,"sub":"u"}' % FAR, "hmac", dict(BASE_CTX, required=["sub"])),
    ("alg outside the allowlist", '{"alg":"HS256"}', '{"exp":%d}' % FAR,
     "hmac", dict(BASE_CTX, allow=["HS384"])),
    ("alg none", '{"alg":"none"}', '{"exp":%d}' % FAR, "empty", BASE_CTX),
    ("empty signature", '{"alg":"HS256"}', '{"exp":%d}' % FAR, "empty",
     BASE_CTX),
    ("payload not JSON", '{"alg":"HS256"}', 'Payload', "hmac", BASE_CTX),
    ("payload a JSON array", '{"alg":"HS256"}', '[1,2]', "hmac", BASE_CTX),
    ("header an array", '["HS256"]', '{"exp":%d}' % FAR, "hmac", BASE_CTX),
    ("repeat inside a nested object", '{"alg":"HS256"}',
     '{"exp":%d,"ctx":{"a":1,"a":2}}' % FAR, "hmac", BASE_CTX),
]


def b64url(raw):
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode()


def probe_token(header_text, claims_text, sig_kind):
    signing_input = (b64url(header_text.encode("utf-8")) + "." +
                     b64url(claims_text.encode("utf-8")))
    if sig_kind == "empty":
        return signing_input + "."
    mac = hmac.new(PROBE_KEY.encode(), signing_input.encode("ascii"),
                   hashlib.sha256).digest()
    return signing_input + "." + b64url(mac)


def pyjwt_verdict(token, ctx):
    try:
        jwt.decode(token, PROBE_KEY, algorithms=ctx["allow"],
                   issuer=ctx["issuer"], audience=ctx["audience"],
                   options={"require": ctx["required"]})
        return "accept"
    except Exception as e:  # every PyJWT refusal is an exception
        return "reject (%s)" % type(e).__name__


def main():
    rsa_key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    ec_key = ec.generate_private_key(ec.SECP256R1())

    payloads = [
        {"iss": "joe", "exp": 2000000000, "nbf": 1400000000,
         "iat": 1400000000, "aud": "api", "sub": "user-1"},
        {"iss": "issuer.example", "exp": 2000000000, "aud": ["api", "web"]},
        {"exp": 2000000000},
        {"iss": "joe", "exp": 1200000000, "aud": "api"},
        {"iss": "jé", "exp": 2000000000, "name": "José"},
        {"iss": "joe", "exp": 2000000000, "nbf": 1600000000},
        {"iss": "joe", "exp": 9999999999, "aud": ["a", "b", "c"],
         "admin": True},
        {"iss": "joe", "exp": 2000000000, "scope": ["read", "write"],
         "n": 42},
    ]
    builders = []
    for p in payloads:
        builders.append(("HS256", jwt.encode(p, "secret", algorithm="HS256")))
        builders.append(("none", jwt.encode(p, "", algorithm="none")))
    builders.append(("RS256", jwt.encode(payloads[0], rsa_key,
                                         algorithm="RS256")))
    builders.append(("RS256", jwt.encode(payloads[1], rsa_key,
                                         algorithm="RS256")))
    builders.append(("ES256", jwt.encode(payloads[0], ec_key,
                                         algorithm="ES256")))
    builders.append(("ES256", jwt.encode(payloads[6], ec_key,
                                         algorithm="ES256")))

    tokens = []
    for alg, tok in builders:
        tokens.append({
            "alg": alg,
            "token": tok,
            "header": jwt.get_unverified_header(tok),
            "claims": jwt.decode(tok, options={"verify_signature": False}),
        })

    probe_now = int(time.time())
    probes = []
    for name, header_text, claims_text, sig_kind, ctx in PROBES:
        tok = probe_token(header_text, claims_text, sig_kind)
        probes.append({
            "name": name,
            "token": tok,
            "context": ctx,
            "pyjwt": pyjwt_verdict(tok, ctx),
        })
    if int(time.time()) - probe_now > 60:
        raise RuntimeError("the probes took too long to stay at one time")

    out = {
        "pyjwt": jwt.__version__,
        "cryptography": cryptography.__version__,
        "probe_now": probe_now,
        "tokens": tokens,
        "probes": probes,
    }
    OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print("wrote %d tokens and %d probes to %s"
          % (len(tokens), len(probes), OUT))
    return 0


if __name__ == "__main__":
    sys.exit(main())
