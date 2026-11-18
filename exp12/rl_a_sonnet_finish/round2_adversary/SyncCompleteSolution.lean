import Sync
import SyncLaws

open Sync

namespace SyncComplete

theorem adj_T (c : Config) (s : Entry) :
    (adjust c s).id = s.id ∧ (adjust c s).adapter = s.adapter ∧ (adjust c s).model = s.model := by
  simp [adjust]; split <;> simp

theorem key (c : Config) : ∀ (L new : List Entry),
    new.map (fun e => (e.id, e.adapter, e.model)) = L.map (fun e => (e.id, e.adapter, e.model)) →
    (∀ x ∈ new, ∀ s ∈ L, x.id = s.id → x.enabled = (adjust c s).enabled) →
    new = L.map (adjust c) := by
  intro L
  induction L with
  | nil => intro new h _; simpa using h
  | cons s L ih =>
    intro new h hen
    cases new with
    | nil => simp at h
    | cons x new =>
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
      have he := hen x (by simp) s (by simp) h1
      obtain ⟨a1, a2, a3⟩ := adj_T c s
      have hx : x = adjust c s := by
        cases x; cases hA : adjust c s; simp_all
      rw [hx]
      exact congrArg _ (ih new h4 (fun y hy t ht => hen y (by simp [hy]) t (by simp [ht])))

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  have fact : ∀ (f : SyncImpl), Passes f → ∀ c st r, DistinctIds st →
      f c st r = r ++ (st.filter (absent r)).map (adjust c) := by
    intro f hf c st r hd
    obtain ⟨_, _, _, _, hdis, hen, hlock, _, _, hone⟩ := hf
    obtain ⟨new, hnew, hmap⟩ := hone c st r
    rw [hnew]
    congr 1
    apply key c _ new hmap
    intro x hx s hs hid
    have hs' := List.mem_filter.mp hs
    have hxm : x ∈ f c st r := by rw [hnew]; simp [hx]
    obtain ⟨a1, a2, a3⟩ := adj_T c s
    cases hE : c.enable
    · rw [hdis c st r hd hE s hs'.1 hs'.2 x hxm hid]; simp only [adjust, hE]; split <;> simp_all
    · cases hL : c.locked s.adapter
      · rw [hen c st r hd hE s hs'.1 hs'.2 hL x hxm hid]; simp only [adjust, hE, hL]; split <;> simp_all
      · rw [hlock c st r hd s hs'.1 hs'.2 hL x hxm hid]; simp only [adjust, hE, hL]; split <;> simp_all
  intro f g hf hg c st r hd
  rw [fact f hf c st r hd, fact g hg c st r hd]

end SyncComplete
