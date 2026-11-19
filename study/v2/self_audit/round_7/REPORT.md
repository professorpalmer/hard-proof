# hpflow audit of hard-proof-repo at e0dd1d3baf0a

Verifiers: claude-sonnet-5-5, claude-opus-5-5. A claim is confirmed (grade 2) when each verifier says `real`.
When the first verifier does not say `real` for a claim of a group, the other verifiers can be absent for that group.
Grade 2 is the agreement of two agents, not a proof. The owner of the code decides what is a bug.

Confirmed bugs after duplicates fold: 0.

## Confirmed (0)

None.

## Real but not reachable (3)

| Function | Claim | Same as | Verdicts | Result now | What goes wrong | Caller |
| --- | --- | --- | --- | --- | --- | --- |
| `tool/hpflow/codexhome.py:first_key` k=1 | first_key turns a surrogate escape such as \ud800 (not a Unicode scalar value, so not a valid TOML escape) into a lone surrogate character, while toml_unescape promises that an escape TOML does not have stays as it is (as it does for \UFFFFFFFF). |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `'\ud800'` | toml_unescape turns a surrogate escape like \ud800 into a lone surrogate (it only checks <= 0x10FFFF) instead of keeping the text as its docstring says, but the only callers just compare the key with dropped names, which neither form can match. |  |
| `tool/hpflow/codexhome.py:toml_unescape` k=1 | A surrogate escape (\uD800..\uDFFF) is not a Unicode scalar value, so TOML has no such escape and it should stay as written, but toml_unescape converts it to a lone surrogate with chr. |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `'a\ud800b'` | A \uD800..\uDFFF escape becomes a lone surrogate instead of staying as written, against the docstring that an escape TOML does not have stays as it is. |  |
| `tool/hpflow/common.py:run_snippet` k=1 | run_snippet runs the child in `tree` but passes HOME=str(home) unresolved (the other paths are made absolute, as the comment says). With a relative `home`, HOME in the child is relative to `tree`, so the home is tree/home, not the given folder. |  | claude-sonnet-5-5: real_unreachable, claude-opus-5-5: None | `{'ok': True, 'result': 'False'}` | With a relative `home`, snippet_env puts a relative HOME in the child, which runs in `tree`, so the home resolves to tree/<home> instead of the given folder. |  |

## By design (0)

None.

## Mixed (0)

None.
