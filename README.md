# jws

A Lean parser for JWS compact serialization. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## Limit, stated up front

This slice does not verify a signature. It must never be described as a verified token on its own. Signature verification is the second slice. A caller that reads claims from this slice without verifying the signature has not checked authenticity.

## First slice

A JSON Web Signature in compact form is three base64url parts joined by dots. The first part is the header. The second part is the payload. The third part is the signature.

- Parse the compact form.
- Decode the header and payload as JSON, using the json repo.
- Read the registered claims exp, nbf, iss, aud, and iat.
- Reject a header with alg set to none.
- Reject an alg outside a caller supplied allowlist.
- Reject a missing required claim, an expired exp, a not yet valid nbf, and a mismatched iss or aud.
- Return the signature bytes unchanged, for a verifier the caller supplies.

## Main claim

Printing a parsed token gives the same token back. A token is accepted only when its framing matches the compact form, its header alg is on the allowlist, and its registered claims pass the checks above.

## Test oracles

- PyJWT and Go JWT libraries.
- RFC 7515 Appendix A and B test vectors.
- RFC 7519 examples.

## Score

16 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- Signature verification.
- Any claim that a token read here is authentic.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
