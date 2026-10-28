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

The corpus holds, for each token PyJWT built: the algorithm, the
token text, and PyJWT's own unverified decode of the header and
the claims. The RS256 and ES256 keys are made fresh on each
rebuild, so their signatures differ between rebuilds; nothing in
the harness depends on signature bytes beyond their being present.
"""

import json
import sys
from pathlib import Path

import cryptography
import jwt
from cryptography.hazmat.primitives.asymmetric import ec, rsa

OUT = Path(__file__).resolve().parent / "pyjwt_corpus.json"


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

    out = {
        "pyjwt": jwt.__version__,
        "cryptography": cryptography.__version__,
        "tokens": tokens,
    }
    OUT.write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print("wrote %d tokens to %s" % (len(tokens), OUT))
    return 0


if __name__ == "__main__":
    sys.exit(main())
