/-
Copyright 2026 Matt Stokes.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjectures.ErdosProblems.«835»

/-!
# Erdős Problem 835: the case where `k + 1` is composite

Formal proofs for statements in `FormalConjectures/ErdosProblems/835.lean`
(google-deepmind/formal-conjectures):

* `Erdos835Proof.not_property_of_not_prime`: if `k ≥ 2` and `k + 1` is not prime, then
  `Erdos835.Property k` fails.
* `Erdos835Proof.property_iff_chromaticNumber`: `χ(J(2k, k)) = k + 1 ↔ Erdos835.Property k`
  for `k > 0`.
* `Erdos835Proof.johnson_chromaticNumber_composite`: `k + 1 < χ(J(2k, k))` for `k > 2` with
  `k + 1` composite.
* `Erdos835Proof.johnson_chromaticNumber_odd` and
  `Erdos835Proof.johnsonGraph_18_9_chromaticNumber`, which follow.

The theorem is due to Ma and Tang
([MT25](https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf)).
This file is a formalization; it claims no new mathematics. The case where `k + 1` is prime,
and so `Erdos835.erdos_835` itself, remains open.

We formalize the following double-counting argument. In a colouring with `Property k`, each
`(k+1)`-set contains exactly one `k`-subset of each colour. Fix a colour and a set `W` with
`#W = k + j`, `1 ≤ j ≤ k`. Counting the pairs `S ⊂ A ⊆ W` with `#S = k`, `S` of that colour and
`#A = k + 1` gives `(k + 1) * #{S ⊆ W of that colour} = (k + j).choose j`. If a prime `p < k + 1`
divides `k + 1`, then `k + 1` does not divide `(k + p).choose p`. Taking `j = p` (allowed, since
`p ≤ k`) gives a contradiction.

Each repository statement is checked against its type with `type_of%` at the end of the file.
-/

open Finset SimpleGraph

namespace Erdos835Proof

/-- If a prime `p < k + 1` divides `k + 1`, then `k + 1` does not divide `(k + p).choose p`. -/
theorem not_dvd_choose (k p : ℕ) (hp : p.Prime) (hpk : p ∣ k + 1) (hlt : p < k + 1) :
    ¬ (k + 1) ∣ (k + p).choose p := by
  rintro ⟨t, ht⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have hA : (k + 1).ascFactorial (q + 1) =
      (q + 1).factorial * (k + (q + 1)).choose (q + 1) :=
    Nat.ascFactorial_eq_factorial_mul_choose k (q + 1)
  rw [Nat.ascFactorial_eq_prod_range, Finset.prod_range_succ', ht, add_zero] at hA
  have hQ : (∏ i ∈ range q, (k + 1 + (i + 1))) = (q + 1).factorial * t := by
    have h2 : (∏ i ∈ range q, (k + 1 + (i + 1))) * (k + 1) =
        ((q + 1).factorial * t) * (k + 1) := by
      rw [hA]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hdvd : q + 1 ∣ ∏ i ∈ range q, (k + 1 + (i + 1)) := by
    rw [hQ]; exact Dvd.dvd.mul_right (Nat.dvd_factorial (by omega) le_rfl) t
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have h3 : q + 1 ∣ i + 1 := (Nat.dvd_add_right hpk).mp hdi
  have h4 := Finset.mem_range.mp hi
  have h5 := Nat.le_of_dvd (by omega) h3
  omega

variable {α : Type*} [DecidableEq α]

/-- For `s ⊆ W`, the `(#s + 1)`-subsets of `W` that strictly contain `s` number `#W - #s`. -/
lemma card_supersets (W s : Finset α) (hsW : s ⊆ W) :
    #((powersetCard (#s + 1) W).filter (fun A => s ⊂ A)) = #W - #s := by
  have himg : (powersetCard (#s + 1) W).filter (fun A => s ⊂ A) =
      (W \ s).image (fun x => insert x s) := by
    ext A
    simp only [mem_filter, mem_powersetCard, mem_image, mem_sdiff]
    constructor
    · rintro ⟨⟨hAW, hAc⟩, hsA⟩
      obtain ⟨a, ha, rfl⟩ := (Finset.exists_eq_insert_iff).mpr ⟨hsA.subset, hAc.symm⟩
      exact ⟨a, ⟨hAW (mem_insert_self a s), ha⟩, rfl⟩
    · rintro ⟨x, ⟨hxW, hxs⟩, rfl⟩
      exact ⟨⟨insert_subset hxW hsW, card_insert_of_notMem hxs⟩, ssubset_insert hxs⟩
  rw [himg, card_image_of_injOn, card_sdiff_of_subset hsW]
  intro x hx y hy hxy
  simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hx hy
  have hxy' : insert x s = insert y s := hxy
  have : x ∈ insert y s := hxy' ▸ mem_insert_self x s
  rcases mem_insert.mp this with h | h
  · exact h
  · exact absurd h hx.2

variable {k : ℕ}

/-- The `k`-subsets strictly inside a `(k+1)`-set: there are `k + 1` of them. -/
lemma card_ssubsets {A : Finset (Fin (2 * k))} (hA : #A = k + 1) :
    #({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = k + 1 := by
  have hmap : ({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}).map
      ⟨Subtype.val, Subtype.val_injective⟩ = powersetCard k A := by
    ext B
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
      mem_powersetCard]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨hs.subset, s.2⟩
    · rintro ⟨hBA, hBc⟩
      refine ⟨⟨B, hBc⟩, ssubset_of_subset_of_ne hBA ?_, rfl⟩
      intro h
      have h' : B = A := h
      rw [h'] at hBc
      omega
  rw [← card_map ⟨Subtype.val, Subtype.val_injective⟩, hmap, card_powersetCard, hA]
  simp

/-- In a `Property k` colouring, each `(k+1)`-set has exactly one `k`-subset of each colour. -/
lemma card_color_in (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (A : Finset (Fin (2 * k))) (hA : #A = k + 1) (i : Fin (k + 1)) :
    #({s | s.val ⊂ A ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) = 1 := by
  set T : Finset {s : Finset (Fin (2 * k)) // #s = k} := {s | s.val ⊂ A} with hTdef
  have hinj : Set.InjOn c T := by
    rw [← card_image_iff, hc A hA, card_univ, Fintype.card_fin, card_ssubsets hA]
  have hfilt : ({s | s.val ⊂ A ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) =
      T.filter (fun s => c s = i) := by
    ext s; simp [hTdef]
  rw [hfilt, card_eq_one]
  have hi : i ∈ image c T := by rw [hc A hA]; exact mem_univ i
  obtain ⟨s, hsT, hsi⟩ := mem_image.mp hi
  refine ⟨s, ?_⟩
  ext t
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨htT, hti⟩
    exact hinj htT hsT (hti.trans hsi.symm)
  · rintro rfl
    exact ⟨hsT, hsi⟩

/-- Double counting: for any colour `i` and `W` with `#W = k + j`, `1 ≤ j`,
`(k + 1) * #{k-subsets of W of colour i} = (k + j).choose j`. -/
lemma color_count (c : {s : Finset (Fin (2 * k)) // #s = k} → Fin (k + 1))
    (hc : ∀ A : Finset (Fin (2 * k)), #A = k + 1 → image c {s | s.val ⊂ A} = univ)
    (i : Fin (k + 1)) (j : ℕ) (hj : 1 ≤ j) (W : Finset (Fin (2 * k))) (hW : #W = k + j) :
    (k + 1) * #({s | s.val ⊆ W ∧ c s = i} : Finset {s : Finset (Fin (2 * k)) // #s = k}) =
      (k + j).choose j := by
  set S : Finset {s : Finset (Fin (2 * k)) // #s = k} := {s | s.val ⊆ W ∧ c s = i} with hSdef
  have hdc := card_mul_eq_card_mul
      (fun (s : {s : Finset (Fin (2 * k)) // #s = k}) (A : Finset (Fin (2 * k))) => s.val ⊂ A)
      (s := S) (t := powersetCard (k + 1) W) (m := j) (n := 1)
    (by
      intro s hs
      simp only [hSdef, mem_filter, mem_univ, true_and] at hs
      have := card_supersets W s.val hs.1
      rw [s.2, hW] at this
      simp only [bipartiteAbove]
      rw [this]; omega)
    (by
      intro A hA
      rw [mem_powersetCard] at hA
      have h1 := card_color_in c hc A hA.2 i
      simp only [bipartiteBelow]
      rw [← h1]
      congr 1
      ext s
      simp only [hSdef, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, hci⟩, hsA⟩; exact ⟨hsA, hci⟩
      · rintro ⟨hsA, hci⟩; exact ⟨⟨hsA.subset.trans hA.1, hci⟩, hsA⟩)
  rw [card_powersetCard, hW, mul_one] at hdc
  have hid : (k + j).choose (k + 1) * (k + 1) = (k + j).choose j * j := by
    rw [Nat.choose_succ_right_eq, Nat.choose_symm_add]
    congr 1; omega
  have : (k + 1) * #S * j = (k + j).choose j * j := by
    rw [← hid, ← hdc]; ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

/-- Ma–Tang, composite case, for `Erdos835.Property`: if `k + 1` is not prime, `Property k`
fails. -/
theorem not_property_of_not_prime (k : ℕ) (hk : 2 ≤ k) (hnp : ¬ (k + 1).Prime) :
    ¬ Erdos835.Property k := by
  rintro ⟨c, hc⟩
  set p := (k + 1).minFac
  have hpr : p.Prime := Nat.minFac_prime (by omega)
  have hlt : p < k + 1 := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  obtain ⟨W, -, hW⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k + p)
    (by rw [card_univ, Fintype.card_fin]; omega)
  have h := color_count c hc 0 p hpr.one_lt.le W hW
  exact not_dvd_choose k p hpr (Nat.minFac_dvd _) hlt ⟨_, h.symm⟩

/-- Two different `k`-subsets of a `(k+1)`-set are adjacent in `J(2k, k)`. -/
lemma adj_of_ssubset {A : Finset (Fin (2 * k))} (hA : #A = k + 1)
    {s t : {s : Finset (Fin (2 * k)) // #s = k}} (hs : s.val ⊂ A) (ht : t.val ⊂ A)
    (hst : s ≠ t) : J(2 * k, k).Adj s t := by
  rw [johnson_adj]
  have hU : #(s.val ∪ t.val) = k + 1 := by
    apply le_antisymm
    · rw [← hA]; exact card_le_card (union_subset hs.subset ht.subset)
    · have hne : s.val ≠ t.val := fun h => hst (Subtype.ext h)
      have hlt : #s.val < #(s.val ∪ t.val) := by
        apply card_lt_card
        refine ssubset_of_subset_of_ne subset_union_left ?_
        intro h
        have htsub : t.val ⊆ s.val := h ▸ subset_union_right
        exact hne (eq_of_subset_of_card_le htsub (by rw [s.2, t.2])).symm
      rw [s.2] at hlt; omega
  have := card_union_add_card_inter s.val t.val
  rw [hU, s.2, t.2] at this
  omega

/-- A proper `(k+1)`-colouring of `J(2k, k)` has `Property k`. -/
lemma property_of_coloring (C : J(2 * k, k).Coloring (Fin (k + 1))) : Erdos835.Property k := by
  refine ⟨C, fun A hA => eq_univ_of_card _ ?_⟩
  rw [card_image_of_injOn, card_ssubsets hA, Fintype.card_fin]
  intro s hs t ht hst
  by_contra hne
  simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
  exact C.valid (adj_of_ssubset hA hs ht hne) hst

/-- A colouring with `Property k` is a proper colouring of `J(2k, k)`. -/
lemma colorable_of_property (hP : Erdos835.Property k) : J(2 * k, k).Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨Coloring.mk c ?_⟩
  intro s t hadj hct
  have hk : #(s.val ∩ t.val) + 1 = k := hadj
  have hst : s ≠ t := J(2 * k, k).ne_of_adj hadj
  have hU := card_union_add_card_inter s.val t.val
  rw [s.2, t.2] at hU
  have hA : #(s.val ∪ t.val) = k + 1 := by omega
  have hinj : Set.InjOn c ({u | u.val ⊂ s.val ∪ t.val} :
      Finset {s : Finset (Fin (2 * k)) // #s = k}) := by
    rw [← card_image_iff, hc _ hA, card_univ, Fintype.card_fin, card_ssubsets hA]
  have hsub : ∀ u : {s : Finset (Fin (2 * k)) // #s = k},
      u.val ⊆ s.val ∪ t.val → u.val ⊂ s.val ∪ t.val :=
    fun u hu => ssubset_of_subset_of_ne hu (fun h => by have := u.2; rw [h] at this; omega)
  refine hst (hinj ?_ ?_ hct)
  · simpa using hsub s subset_union_left
  · simpa using hsub t subset_union_right

/-- `J(2k, k)` contains a `(k+1)`-clique, so `k + 1 ≤ χ(J(2k, k))` for `k > 0`. -/
lemma le_chromaticNumber (hk : 0 < k) : (k + 1 : ℕ∞) ≤ J(2 * k, k).chromaticNumber := by
  obtain ⟨A, -, hA⟩ := exists_subset_card_eq (s := (univ : Finset (Fin (2 * k)))) (n := k + 1)
    (by rw [card_univ, Fintype.card_fin]; omega)
  have hcl : J(2 * k, k).IsClique
      (({s | s.val ⊂ A} : Finset {s : Finset (Fin (2 * k)) // #s = k}) : Set _) := by
    intro s hs t ht hst
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hs ht
    exact adj_of_ssubset hA hs ht hst
  have := hcl.card_le_chromaticNumber
  rw [card_ssubsets hA] at this
  exact_mod_cast this

/-- The repository statement `property_iff_chromaticNumber`. -/
theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔ Erdos835.Property k := by
  constructor
  · intro h
    have hcol : J(2 * k, k).Colorable (k + 1) := by
      rw [← chromaticNumber_le_iff_colorable, h]; push_cast; exact le_rfl
    exact property_of_coloring (hcol.toColoring (by simp))
  · intro hP
    apply le_antisymm
    · have := (colorable_of_property hP).chromaticNumber_le
      push_cast at this; exact this
    · exact le_chromaticNumber hk

/-- The repository statement `johnson_chromaticNumber_composite` (Ma–Tang, composite case). -/
theorem johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : (k + 1).Composite) :
    k + 1 < J(2 * k, k).chromaticNumber := by
  refine lt_of_le_of_ne (le_chromaticNumber (by omega)) fun heq => ?_
  exact not_property_of_not_prime k (by omega) h.2
    ((property_iff_chromaticNumber k (by omega)).mp heq.symm)

/-- The repository statement `johnson_chromaticNumber_odd`, via the repository's own reduction
`Erdos835.johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite`. -/
theorem johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber :=
  Erdos835.johnsonGraph_chromaticNumber_odd_of_johnson_chromaticNumber_composite
    johnson_chromaticNumber_composite k hk h

/-- The repository statement `johnsonGraph_18_9_chromaticNumber` (`k = 9`, `k + 1 = 10`). -/
theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 :=
  johnson_chromaticNumber_composite 9 (by norm_num) ⟨by norm_num, by norm_num⟩

-- The proofs have exactly the types of the repository statements.
example : type_of% Erdos835.johnson_chromaticNumber_composite :=
  Erdos835Proof.johnson_chromaticNumber_composite
example : type_of% Erdos835.property_iff_chromaticNumber :=
  Erdos835Proof.property_iff_chromaticNumber
example : type_of% Erdos835.johnson_chromaticNumber_odd :=
  Erdos835Proof.johnson_chromaticNumber_odd
example : type_of% Erdos835.johnsonGraph_18_9_chromaticNumber :=
  Erdos835Proof.johnsonGraph_18_9_chromaticNumber

end Erdos835Proof
