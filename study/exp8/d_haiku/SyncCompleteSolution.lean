import SyncLaws

open SyncLaws

namespace SyncComplete

/-- Two entries with one key and one `enabled` value are equal. -/
theorem entry_eq_of (a b : Entry) (h1 : key a = key b) (h2 : a.enabled = b.enabled) : a = b := by
  cases a with
  | mk ai aa am ae =>
  cases b with
  | mk bi ba bm be =>
  simp only [key, Prod.mk.injEq] at h1
  dsimp only at h2
  obtain ⟨rfl, rfl, rfl⟩ := h1
  subst h2
  rfl

/-- Two lists with one key sequence, and equal `enabled` for each key-equal pair, are equal. -/
theorem list_eq_of (A B : List Entry) (h : A.map key = B.map key)
    (hab : ∀ a ∈ A, ∀ b ∈ B, key a = key b → a.enabled = b.enabled) : A = B := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => rfl
    | cons b B' => simp at h
  | cons a A ih =>
    cases B with
    | nil => simp at h
    | cons b B' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have hen : a.enabled = b.enabled := hab a (by simp) b (by simp) h1
      have hrest : A = B' := by
        refine ih B' h2 ?_
        intro x hx y hy hk
        exact hab x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem b hy) hk
      rw [entry_eq_of a b h1 hen, hrest]

/-- What a passing design says about each added row, given the settings. -/
theorem det_of {f : SyncImpl} (hf : Passes f) {c : Config} {st r added : List Entry}
    (hd : DistinctIds st) (h : f c st r = r ++ added) {a : Entry} (ha : a ∈ added) :
    (c.enable = false → a.enabled = false) ∧
    (c.locked a.adapter = true → a.enabled = false) ∧
    (c.enable = true → c.locked a.adapter = false →
      ∃ s ∈ st, s.id = a.id ∧ a.enabled = s.enabled) := by
  obtain ⟨_, _, _, hdis, hlock, hen, _, _⟩ := hf
  exact ⟨fun hc => hdis c st r added hc h a ha,
    fun hl => hlock c st r added h a ha hl,
    fun he hu => hen c st r added hd he h a ha hu⟩

/-- Two passing designs agree on the `enabled` value of any two added rows with one key. -/
theorem enabled_agree {f g : SyncImpl} (hf : Passes f) (hg : Passes g) {c : Config}
    {st r A B : List Entry} (hd : DistinctIds st) (hA : f c st r = r ++ A)
    (hB : g c st r = r ++ B) {a b : Entry} (ha : a ∈ A) (hb : b ∈ B) (hk : key a = key b) :
    a.enabled = b.enabled := by
  obtain ⟨fa1, fa2, fa3⟩ := det_of hf hd hA ha
  obtain ⟨gb1, gb2, gb3⟩ := det_of hg hd hB hb
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨hid, had, _⟩ := hk
  by_cases he : c.enable = true
  · by_cases hl : c.locked a.adapter = true
    · rw [fa2 hl, gb2 (by rw [← had]; exact hl)]
    · have hl' : c.locked a.adapter = false := by simpa using hl
      obtain ⟨s, hs, hsid, hse⟩ := fa3 he hl'
      obtain ⟨t, ht, htid, hte⟩ := gb3 he (by rw [← had]; exact hl')
      have hst : s = t := hd s hs t ht (by rw [hsid, htid]; exact hid)
      rw [hse, hte, hst]
  · have he' : c.enable = false := by simpa using he
    rw [fa1 he', gb1 he']

/-- The laws are complete. -/
theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  obtain ⟨A, hA⟩ := hf.1 c st r
  obtain ⟨B, hB⟩ := hg.1 c st r
  have hAk : A.map key = (st.filter (absent r)).map key := hf.2.2.2.2.2.2.2 c st r A hA
  have hBk : B.map key = (st.filter (absent r)).map key := hg.2.2.2.2.2.2.2 c st r B hB
  rw [hA, hB]
  congr 1
  apply list_eq_of A B (hAk.trans hBk.symm)
  intro a ha b hb hk
  exact enabled_agree hf hg hd hA hB ha hb hk

end SyncComplete
