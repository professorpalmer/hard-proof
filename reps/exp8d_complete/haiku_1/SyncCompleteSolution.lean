import SyncLaws

open SyncLaws

namespace SyncComplete

/-- Two lists of entries with the same key list and the same key-to-entry map are equal. -/
theorem list_eq_of_map_key (xs : List Entry) : ∀ (ys : List Entry), xs.map key = ys.map key →
    (∀ a ∈ xs, ∀ b ∈ ys, key a = key b → a = b) → xs = ys := by
  induction xs with
  | nil =>
    intro ys h _
    cases ys with
    | nil => rfl
    | cons b ys => simp at h
  | cons a xs ih =>
    intro ys h hp
    cases ys with
    | nil => simp at h
    | cons b ys =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hab : a = b := hp a (by simp) b (by simp) h.1
      have ih' := ih ys h.2 (fun a' ha' b' hb' hk => hp a' (by simp [ha']) b' (by simp [hb']) hk)
      subst hab
      rw [ih']

/-- Under any passing design, the `enabled` flag of an added entry is fixed by
its starter entry: `--enable` off or locked gives false, otherwise the starter flag. -/
theorem enabled_eq (f : SyncImpl) (hf : Passes f) (c : Config) (st r added : List Entry)
    (hd : DistinctIds st) (h : f c st r = r ++ added) (a : Entry) (ha : a ∈ added)
    (s0 : Entry) (hs0 : s0 ∈ st) (hk : key s0 = key a) :
    a.enabled = (c.enable && !c.locked a.adapter && s0.enabled) := by
  obtain ⟨_, _, _, hDis, hLock, hEn, _, _⟩ := hf
  have hid : s0.id = a.id := by
    simp only [key, Prod.mk.injEq] at hk
    exact hk.1
  cases hce : c.enable with
  | false =>
    have := hDis c st r added hce h a ha
    simp [this]
  | true =>
    cases hl : c.locked a.adapter with
    | true =>
      have := hLock c st r added h a ha hl
      simp [this]
    | false =>
      obtain ⟨s, hs, hsid, hen⟩ := hEn c st r added hd hce h a ha hl
      have hss : s = s0 := hd s hs s0 hs0 (by rw [hsid, hid])
      subst hss
      simp [hen]

theorem laws_complete : ∀ (f g : SyncImpl), Passes f → Passes g →
    ∀ (c : Config) (st r : List Entry), DistinctIds st → f c st r = g c st r := by
  intro f g hf hg c st r hd
  have hf0 := hf
  have hg0 := hg
  obtain ⟨hKf, _, _, _, _, _, _, hEf⟩ := hf
  obtain ⟨hKg, _, _, _, _, _, _, hEg⟩ := hg
  obtain ⟨addF, hF⟩ := hKf c st r
  obtain ⟨addG, hG⟩ := hKg c st r
  rw [hF, hG]
  congr 1
  apply list_eq_of_map_key addF addG
  · rw [hEf c st r addF hF, hEg c st r addG hG]
  · intro a ha b hb hk
    have hmemA : key a ∈ addF.map key := List.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hEf c st r addF hF] at hmemA
    obtain ⟨s0, hs0, hk0⟩ := List.mem_map.mp hmemA
    have hs0' := (List.mem_filter.mp hs0).1
    have hmemB : key b ∈ addG.map key := List.mem_map.mpr ⟨b, hb, rfl⟩
    rw [hEg c st r addG hG] at hmemB
    obtain ⟨s1, hs1, hk1⟩ := List.mem_map.mp hmemB
    have hs1' := (List.mem_filter.mp hs1).1
    have hea := enabled_eq f hf0 c st r addF hd hF a ha s0 hs0' hk0
    have heb := enabled_eq g hg0 c st r addG hd hG b hb s1 hs1' hk1
    have hkk0 := hk0
    have hkk1 := hk1
    have hkk := hk
    simp only [key, Prod.mk.injEq] at hkk0 hkk1 hkk
    have hid : s0.id = s1.id := hkk0.1.trans (hkk.1.trans hkk1.1.symm)
    have hs : s0 = s1 := hd s0 hs0' s1 hs1' hid
    subst hs
    rw [hkk.2.1] at hea
    have hen : a.enabled = b.enabled := hea.trans heb.symm
    cases a with
    | mk i1 a1 m1 e1 =>
      cases b with
      | mk i2 a2 m2 e2 =>
        simp only [] at hkk hen
        obtain ⟨h1, h2, h3⟩ := hkk
        subst h1; subst h2; subst h3; subst hen
        rfl

end SyncComplete
