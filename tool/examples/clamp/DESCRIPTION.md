# clamp: the documentation sentences

Source file: `pycode/clampmod.py` (docstring of `clamp`).

1. "Return x limited to the closed range from lo to hi."
2. "When x is less than lo, the result is lo."
3. "When x is more than hi, the result is hi."
4. "Else the result is x."
5. "The caller must give lo <= hi."

## Model words and documentation words

| Model word | Documentation word |
| --- | --- |
| `Input.x`, `Input.lo`, `Input.hi` | the arguments `x`, `lo`, `hi` |
| `Output` | the result |
| `Legal` | "The caller must give lo <= hi." |
