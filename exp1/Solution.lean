/-
Hard Proof, experiment 1. AGENT-OWNED FILE.

The lock design and the evidence for each challenge theorem.
-/
import Laws
import Mutants

open Laws

namespace Exp

/-- The lock stores the pid and the start token. -/
def lock : LockImpl where
  Rec := Proc
  record p := p
  alive os r := decide (os.table r.pid = some r.tok)
  isOwner r p := decide (r = p)

/-! ## Replay induction -/

theorem foldl_inv {I : LockImpl} (P : State I → Prop)
    (hs : ∀ s e, P s → P (step I s e)) :
    ∀ (evs : List Event) (s : State I), P s → P (evs.foldl (step I) s) := by
  intro evs
  induction evs with
  | nil => intro s h; exact h
  | cons e es ih => intro s h; exact ih _ (hs s e h)

theorem replay_inv {I : LockImpl} (P : State I → Prop)
    (h0 : P (init I)) (hs : ∀ s e, P s → P (step I s e)) (evs : List Event) :
    P (replay I evs) :=
  foldl_inv P hs evs (init I) h0

theorem proc_eq {p : Proc} {pid t : Nat} (h1 : p.pid = pid) (h2 : p.tok = t) :
    p = ⟨pid, t⟩ := by
  subst h1; subst h2; rfl

/-! ## The lock with a start token -/

/-- The inductive invariant. The two "fresh" fields are the part that the laws
do not state: no stored token is equal to a token that the OS gives later. -/
structure Inv (s : State lock) : Prop where
  freshT : ∀ (pid t : Nat), s.os.table pid = some t → t < s.os.next
  freshO : ∀ r : Proc, s.owner = some r → r.tok < s.os.next
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p ∧ s.os.table p.pid = some p.tok
  ownerCs : ∀ r : Proc, s.owner = some r → s.os.table r.pid = some r.tok → s.cs r = true

theorem inv_init : Inv (init lock) := by
  constructor <;> simp [init]

theorem inv_step (s : State lock) (e : Event) (h : Inv s) : Inv (step lock s e) := by
  obtain ⟨hT, hO, hC, hOC⟩ := h
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | none =>
      simp only [step, hpid]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q t hq
        show t < s.os.next + 1
        have hq' : (if q = pid then some s.os.next else s.os.table q) = some t := hq
        split at hq'
        · have : s.os.next = t := Option.some.inj hq'
          omega
        · have := hT q t hq'
          omega
      · intro r hr
        show r.tok < s.os.next + 1
        have := hO r hr
        omega
      · intro p hp
        obtain ⟨h1, h2⟩ := hC p hp
        refine ⟨h1, ?_⟩
        show (if p.pid = pid then some s.os.next else s.os.table p.pid) = some p.tok
        have hne : p.pid ≠ pid := by
          intro heq; rw [heq, hpid] at h2; cases h2
        simp only [hne, ↓reduceIte]; exact h2
      · intro r hr hlive
        have hlive' :
            (if r.pid = pid then some s.os.next else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · have h1 : s.os.next = r.tok := Option.some.inj hlive'
          have h2 := hO r hr
          omega
        · exact hOC r hr hlive'
  | exit pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      simp only [step, hpid]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro q t hq
        show t < s.os.next
        have hq' : (if q = pid then none else s.os.table q) = some t := hq
        split at hq'
        · cases hq'
        · exact hT q t hq'
      · intro r hr; exact hO r hr
      · intro p hp
        have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
        split at hp'
        · cases hp'
        · rename_i hne
          obtain ⟨h1, h2⟩ := hC p hp'
          refine ⟨h1, ?_⟩
          show (if p.pid = pid then none else s.os.table p.pid) = some p.tok
          have hpne : p.pid ≠ pid := by
            intro heq
            apply hne
            rw [heq, hpid] at h2
            exact proc_eq heq (Option.some.inj h2).symm
          simp only [hpne, ↓reduceIte]; exact h2
      · intro r hr hlive
        have hlive' : (if r.pid = pid then none else s.os.table r.pid) = some r.tok := hlive
        split at hlive'
        · cases hlive'
        · rename_i hne
          have hcs := hOC r hr hlive'
          show (if r = ⟨pid, t0⟩ then false else s.cs r) = true
          have hrne : r ≠ ⟨pid, t0⟩ := by
            intro heq; apply hne; rw [heq]
          simp only [hrne, ↓reduceIte]; exact hcs
  | acquire pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      simp only [step, hpid]
      cases hg : grants lock s with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
      | true =>
        simp only [↓reduceIte]
        have hempty : ∀ p : Proc, s.cs p = false := by
          intro p
          cases hcs : s.cs p with
          | false => rfl
          | true =>
            obtain ⟨h1, h2⟩ := hC p hcs
            simp [grants, h1, h2, lock] at hg
        refine ⟨hT, ?_, ?_, ?_⟩
        · intro r hr
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          show r.tok < s.os.next
          rw [← hr']; exact hT pid t0 hpid
        · intro p hp
          have hp' : (if p = ⟨pid, t0⟩ then true else s.cs p) = true := hp
          split at hp'
          · rename_i heq
            subst heq
            exact ⟨rfl, hpid⟩
          · rw [hempty p] at hp'; cases hp'
        · intro r hr _
          have hr' : (⟨pid, t0⟩ : Proc) = r := Option.some.inj hr
          show (if r = ⟨pid, t0⟩ then true else s.cs r) = true
          subst hr'; simp
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hT, hO, hC, hOC⟩
    | some t0 =>
      cases ho : s.owner with
      | none => simp only [step, hpid, ho]; exact ⟨hT, hO, hC, hOC⟩
      | some r =>
        simp only [step, hpid, ho]
        cases hio : lock.isOwner r ⟨pid, t0⟩ with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hT, hO, hC, hOC⟩
        | true =>
          simp only [↓reduceIte]
          have hrp : r = (⟨pid, t0⟩ : Proc) := by simpa [lock] using hio
          refine ⟨hT, ?_, ?_, ?_⟩
          · intro r' hr'
            have hr'' : (none : Option Proc) = some r' := hr'
            cases hr''
          · intro p hp
            have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
            split at hp'
            · cases hp'
            · rename_i hne
              obtain ⟨h1, _⟩ := hC p hp'
              rw [ho] at h1
              have hrp' : r = p := Option.some.inj h1
              exact absurd (hrp' ▸ hrp) hne
          · intro r' hr'
            have hr'' : (none : Option Proc) = some r' := hr'
            cases hr''

theorem inv_all (evs : List Event) : Inv (replay lock evs) :=
  replay_inv Inv inv_init inv_step evs

theorem mutex : Mutex lock := by
  intro evs p q hp hq
  have h := inv_all evs
  have h1 := (h.csOwner p hp).1
  have h2 := (h.csOwner q hq).1
  rw [h1] at h2
  exact Option.some.inj h2

theorem no_orphan_hold : NoOrphanHold lock := by
  intro evs hg
  have h := inv_all evs
  cases ho : (replay lock evs).owner with
  | none => simp [grants, ho] at hg
  | some r =>
    have hg' : (!(lock.alive (replay lock evs).os r)) = false := by
      simpa [grants, ho] using hg
    have halive : (replay lock evs).os.table r.pid = some r.tok := by
      simpa [lock] using hg'
    exact ⟨r, h.ownerCs r ho halive, halive⟩

theorem can_refuse : CanRefuse lock := ⟨[.spawn 5, .acquire 5], by decide⟩

theorem can_enter : CanEnter lock := ⟨[.spawn 5, .acquire 5], ⟨5, 0⟩, by decide⟩

/-! ## The pid-only mutant -/

/-- Law 2 is false for the pid-only lock. Process A takes the lock and exits.
A new process gets the same pid. The lock now refuses each request, and the
critical section is empty. -/
theorem kill_pid_only : ¬ NoOrphanHold Mutants.pidOnly := by
  intro h
  obtain ⟨q, hq, _⟩ := h [.spawn 5, .acquire 5, .exit 5, .spawn 5] (by decide)
  have hq' : (if q = ⟨5, 0⟩ then false else (if q = ⟨5, 0⟩ then true else false)) = true := hq
  split at hq'
  · cases hq'
  · cases hq'

/-- The invariant for the pid-only lock. It is sufficient for Law 1. -/
structure InvM (s : State Mutants.pidOnly) : Prop where
  csOwner : ∀ p : Proc, s.cs p = true → s.owner = some p.pid ∧ s.os.table p.pid = some p.tok

theorem invM_init : InvM (init Mutants.pidOnly) := by
  constructor; simp [init]

theorem invM_step (s : State Mutants.pidOnly) (e : Event) (h : InvM s) :
    InvM (step Mutants.pidOnly s e) := by
  obtain ⟨hC⟩ := h
  cases e with
  | spawn pid =>
    cases hpid : s.os.table pid with
    | some t0 => simp only [step, hpid]; exact ⟨hC⟩
    | none =>
      simp only [step, hpid]
      refine ⟨?_⟩
      intro p hp
      obtain ⟨h1, h2⟩ := hC p hp
      refine ⟨h1, ?_⟩
      show (if p.pid = pid then some s.os.next else s.os.table p.pid) = some p.tok
      have hne : p.pid ≠ pid := by
        intro heq; rw [heq, hpid] at h2; cases h2
      simp only [hne, ↓reduceIte]; exact h2
  | exit pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hC⟩
    | some t0 =>
      simp only [step, hpid]
      refine ⟨?_⟩
      intro p hp
      have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
      split at hp'
      · cases hp'
      · rename_i hne
        obtain ⟨h1, h2⟩ := hC p hp'
        refine ⟨h1, ?_⟩
        show (if p.pid = pid then none else s.os.table p.pid) = some p.tok
        have hpne : p.pid ≠ pid := by
          intro heq
          apply hne
          rw [heq, hpid] at h2
          exact proc_eq heq (Option.some.inj h2).symm
        simp only [hpne, ↓reduceIte]; exact h2
  | acquire pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hC⟩
    | some t0 =>
      simp only [step, hpid]
      cases hg : grants Mutants.pidOnly s with
      | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hC⟩
      | true =>
        simp only [↓reduceIte]
        have hempty : ∀ p : Proc, s.cs p = false := by
          intro p
          cases hcs : s.cs p with
          | false => rfl
          | true =>
            obtain ⟨h1, h2⟩ := hC p hcs
            simp [grants, h1, h2, Mutants.pidOnly] at hg
        refine ⟨?_⟩
        intro p hp
        have hp' : (if p = ⟨pid, t0⟩ then true else s.cs p) = true := hp
        split at hp'
        · rename_i heq
          subst heq
          exact ⟨rfl, hpid⟩
        · rw [hempty p] at hp'; cases hp'
  | release pid =>
    cases hpid : s.os.table pid with
    | none => simp only [step, hpid]; exact ⟨hC⟩
    | some t0 =>
      cases ho : s.owner with
      | none => simp only [step, hpid, ho]; exact ⟨hC⟩
      | some r =>
        simp only [step, hpid, ho]
        cases hio : Mutants.pidOnly.isOwner r ⟨pid, t0⟩ with
        | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hC⟩
        | true =>
          simp only [↓reduceIte]
          have hrp : r = pid := @eq_of_beq Nat _ _ r pid hio
          refine ⟨?_⟩
          intro p hp
          have hp' : (if p = ⟨pid, t0⟩ then false else s.cs p) = true := hp
          split at hp'
          · cases hp'
          · rename_i hne
            obtain ⟨h1, h2⟩ := hC p hp'
            rw [ho] at h1
            have hr : r = p.pid := Option.some.inj h1
            have hpp : p.pid = pid := hr.symm.trans hrp
            rw [hpp, hpid] at h2
            exact absurd (proc_eq hpp (Option.some.inj h2).symm) hne

/-- Law 1 is true for the pid-only lock. Law 1 alone cannot catch the bug. -/
theorem mutex_alone_misses_pid_only : Mutex Mutants.pidOnly := by
  intro evs p q hp hq
  have h := replay_inv InvM invM_init invM_step evs
  obtain ⟨hp1, hp2⟩ := h.csOwner p hp
  obtain ⟨hq1, hq2⟩ := h.csOwner q hq
  have hpid : p.pid = q.pid := Option.some.inj (hp1.symm.trans hq1)
  rw [hpid] at hp2
  have htok : p.tok = q.tok := Option.some.inj (hp2.symm.trans hq2)
  have hq' : q = ⟨q.pid, q.tok⟩ := rfl
  rw [hq']
  exact proc_eq hpid htok

end Exp
