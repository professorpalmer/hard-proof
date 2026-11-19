# The stale-lock recovery rule, in the words of the code's own documentation

These sentences are from the docstrings of `puppetmaster/interprocess_lock.py`.

1. "Lock ownership is recorded with a PID and a random token. A later process
   recovers an orphan whose owner PID is no longer alive; malformed/unknown
   owners are recovered after `stale_after` seconds."
2. "`stale_after` is only used when an owner cannot be identified safely."
3. "Remove only an orphaned lock, with a guard against reclaim races. The owner
   is gone when its pid is dead or now names a later process (the lock records
   the owner's identity, see `proc_identity`)."
