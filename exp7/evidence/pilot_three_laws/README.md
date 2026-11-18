# Completeness with three of the four lock laws

`Complete.lean` proves that `Mutex`, `NoOrphanHold` and `ReleaseFrees` (laws 1, 2 and 4) are sufficient for the completeness result of the lock domain. Law 3 (`HolderKeepsLock`) is not a hypothesis. The pilot wrote this proof before the worker runs of experiment 7. `Laws.lean` here is the law file of experiment 6 and `Complete.lean` defines law 4 locally with the same statement as `exp7/base/Laws.lean`.

Check: `lake build && lake env lean Axioms.lean`.
