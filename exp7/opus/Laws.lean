/-
Hard Proof, experiment 7. HUMAN-OWNED FILE.

This file is the law cone. It holds the world model, the laws, and the pinned
examples. The gate rejects a run when the hash of this file is not the signed
hash. The agent cannot edit this file.

World: an operating system that can give a pid to a new process after the old
process exits. Each process start gets a new start token.

Code under test: a lock design (`LockImpl`). The design selects what the lock
stores about its owner, and how the lock decides that the owner is alive.
-/

namespace Laws

/-- A process identity: the pid, and the start token from the kernel. -/
structure Proc where
  pid : Nat
  tok : Nat
deriving DecidableEq, Repr

/-- The operating system: the token of the live process at each pid, and the
next start token. -/
structure OS where
  table : Nat → Option Nat
  next : Nat

/-- Process `p` is alive. -/
def OS.live (os : OS) (p : Proc) : Prop := os.table p.pid = some p.tok

instance (os : OS) (p : Proc) : Decidable (os.live p) :=
  inferInstanceAs (Decidable (os.table p.pid = some p.tok))

/-- A lock design. This is the code under test. -/
structure LockImpl where
  /-- What the lock stores about its owner. -/
  Rec : Type
  /-- The record that the lock writes at an acquire. -/
  record : Proc → Rec
  /-- The lock decides if the owner in a record is alive. -/
  alive : OS → Rec → Bool
  /-- The lock decides if process `p` is the owner in a record. -/
  isOwner : Rec → Proc → Bool

/-- The system state. `cs` is ghost state: the processes that are in the
critical section. The lock cannot read `cs`. -/
structure State (I : LockImpl) where
  os : OS
  owner : Option I.Rec
  cs : Proc → Bool

inductive Event where
  | spawn (pid : Nat)
  | exit (pid : Nat)
  | acquire (pid : Nat)
  | release (pid : Nat)

def init (I : LockImpl) : State I :=
  { os := { table := fun _ => none, next := 0 }
    owner := none
    cs := fun _ => false }

def setTable (t : Nat → Option Nat) (pid : Nat) (v : Option Nat) : Nat → Option Nat :=
  fun q => if q = pid then v else t q

def setCS (c : Proc → Bool) (p : Proc) (b : Bool) : Proc → Bool :=
  fun q => if q = p then b else c q

/-- The lock grants a request when it has no owner record, or when it decides
that the owner in the record is dead. -/
def grants (I : LockImpl) (s : State I) : Bool :=
  match s.owner with
  | none => true
  | some r => !(I.alive s.os r)

def step (I : LockImpl) (s : State I) : Event → State I
  | .spawn pid =>
    match s.os.table pid with
    | some _ => s
    | none =>
      { s with os := { table := setTable s.os.table pid (some s.os.next)
                       next := s.os.next + 1 } }
  | .exit pid =>
    match s.os.table pid with
    | none => s
    | some t =>
      { s with os := { s.os with table := setTable s.os.table pid none }
               cs := setCS s.cs ⟨pid, t⟩ false }
  | .acquire pid =>
    match s.os.table pid with
    | none => s
    | some t =>
      if grants I s then
        { s with owner := some (I.record ⟨pid, t⟩), cs := setCS s.cs ⟨pid, t⟩ true }
      else s
  | .release pid =>
    match s.os.table pid with
    | none => s
    | some t =>
      match s.owner with
      | none => s
      | some r =>
        if I.isOwner r ⟨pid, t⟩ then
          { s with owner := none, cs := setCS s.cs ⟨pid, t⟩ false }
        else s

def replay (I : LockImpl) (evs : List Event) : State I :=
  evs.foldl (step I) (init I)

/-! ## Laws -/

/-- Law 1. Two processes are never in the critical section together. -/
def Mutex (I : LockImpl) : Prop :=
  ∀ evs : List Event, ∀ p q : Proc,
    (replay I evs).cs p = true → (replay I evs).cs q = true → p = q

/-- Law 2. When the lock refuses a request, a live process is in the critical
section. A dead owner never blocks the lock. -/
def NoOrphanHold (I : LockImpl) : Prop :=
  ∀ evs : List Event,
    grants I (replay I evs) = false →
      ∃ q : Proc, (replay I evs).cs q = true ∧ (replay I evs).os.live q

/-- Law 3. A process in the critical section keeps the lock. An event that is
not its own release and not its own exit does not change the owner record, and
it does not take the process out of the critical section. -/
def HolderKeepsLock (I : LockImpl) : Prop :=
  ∀ (evs : List Event) (e : Event) (p : Proc),
    (replay I evs).cs p = true →
    e ≠ Event.release p.pid → e ≠ Event.exit p.pid →
      (replay I (evs ++ [e])).owner = (replay I evs).owner ∧
      (replay I (evs ++ [e])).cs p = true

/-- Law 4. A release by the process in the critical section frees the lock.
Added after experiment 6: an adversary showed that laws 1 to 3 allow a lock
that never releases. -/
def ReleaseFrees (I : LockImpl) : Prop :=
  ∀ (evs : List Event) (p : Proc),
    (replay I evs).cs p = true →
      (replay I (evs ++ [Event.release p.pid])).cs p = false

/-! ## Witness statements (the laws are not vacuous) -/

/-- The lock can refuse a request. Without this, Law 2 is empty. -/
def CanRefuse (I : LockImpl) : Prop :=
  ∃ evs : List Event, grants I (replay I evs) = false

/-- A process can enter the critical section. Without this, Law 1 is empty. -/
def CanEnter (I : LockImpl) : Prop :=
  ∃ evs : List Event, ∃ p : Proc, (replay I evs).cs p = true

/-- A design passes when each law and each witness statement holds for it. -/
def Passes (I : LockImpl) : Prop :=
  Mutex I ∧ NoOrphanHold I ∧ HolderKeepsLock I ∧ ReleaseFrees I ∧ CanRefuse I ∧ CanEnter I

/-! ## Pinned examples

These examples pin the vocabulary. A change that makes a definition empty
breaks one of them. `probe` is a lock that always decides "alive". -/

private def probe : LockImpl where
  Rec := Unit
  record _ := ()
  alive _ _ := true
  isOwner _ _ := true

-- A new process is alive, with token 0.
example : (replay probe [.spawn 5]).os.live ⟨5, 0⟩ := by decide
-- A process that exits is dead.
example : ¬ (replay probe [.spawn 5, .exit 5]).os.live ⟨5, 0⟩ := by decide
-- The OS gives the pid again, with a new token.
example : (replay probe [.spawn 5, .exit 5, .spawn 5]).os.live ⟨5, 1⟩ := by decide
example : ¬ (replay probe [.spawn 5, .exit 5, .spawn 5]).os.live ⟨5, 0⟩ := by decide
-- A granted acquire puts the process in the critical section.
example : (replay probe [.spawn 5, .acquire 5]).cs ⟨5, 0⟩ = true := by decide
-- A process that exits is not in the critical section.
example : (replay probe [.spawn 5, .acquire 5, .exit 5]).cs ⟨5, 0⟩ = false := by decide
-- A release takes the process out of the critical section.
example : (replay probe [.spawn 5, .acquire 5, .release 5]).cs ⟨5, 0⟩ = false := by decide
-- A dead process cannot acquire.
example : (replay probe [.acquire 5]).cs ⟨5, 0⟩ = false := by decide
-- A lock with no owner grants. A lock with a live owner refuses.
example : grants probe (replay probe []) = true := by decide
example : grants probe (replay probe [.spawn 5, .acquire 5]) = false := by decide

end Laws
