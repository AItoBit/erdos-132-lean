/-
Copyright 2026 AItoBit and The Formal Conjectures Authors.

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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto


open Finset


namespace Erdos132Proof

/-- The Euclidean plane $\mathbb{R}^2$. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The number of unordered pairs $\{x, y\}$ of distinct points of `A` at distance `d`.
We count ordered pairs and divide by two. The count of ordered pairs is always even. -/
noncomputable def distMult (A : Finset Plane) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/-- The set of distances determined by `A`, i.e. those occurring at least once. -/
noncomputable def distances (A : Finset Plane) : Finset ℝ :=
  A.offDiag.image (fun p => dist p.1 p.2)

/-- The *rare* distances of `A`: distances that occur at least once, but between at most
$n = |A|$ pairs of points. -/
noncomputable def rareDistances (A : Finset Plane) : Finset ℝ :=
  (distances A).filter (fun d => distMult A d ≤ A.card)

/-! ### The four-point example -/

lemma dist_pt (x1 y1 x2 y2 : ℝ) :
    dist (!₂[x1, y1] : Plane) !₂[x2, y2] = Real.sqrt ((x1 - x2) ^ 2 + (y1 - y2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]; simp [Real.dist_eq, sq_abs]

/-- Vertices of the rhombus formed by two unit equilateral triangles glued along an edge. -/
noncomputable def pa : Plane := !₂[0, 0]
noncomputable def pb : Plane := !₂[1, 0]
noncomputable def pc : Plane := !₂[1/2, Real.sqrt 3 / 2]
noncomputable def pd : Plane := !₂[3/2, Real.sqrt 3 / 2]

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma d_ab : dist pa pb = 1 := by
  rw [pa, pb, dist_pt, Real.sqrt_eq_one]; ring_nf

lemma d_ac : dist pa pc = 1 := by
  rw [pa, pc, dist_pt, Real.sqrt_eq_one]; ring_nf; rw [sqrt3_sq]; norm_num

lemma d_ad : dist pa pd = Real.sqrt 3 := by
  rw [pa, pd, dist_pt]; congr 1; ring_nf; rw [sqrt3_sq]; norm_num

lemma d_bc : dist pb pc = 1 := by
  rw [pb, pc, dist_pt, Real.sqrt_eq_one]; ring_nf; rw [sqrt3_sq]; norm_num

lemma d_bd : dist pb pd = 1 := by
  rw [pb, pd, dist_pt, Real.sqrt_eq_one]; ring_nf; rw [sqrt3_sq]; norm_num

lemma d_cd : dist pc pd = 1 := by
  rw [pc, pd, dist_pt, Real.sqrt_eq_one]; ring_nf

/-- The four vertices of the rhombus, indexed by `Fin 4`. -/
noncomputable def rh : Fin 4 → Plane := ![pa, pb, pc, pd]

lemma sqrt3_ne_one : Real.sqrt 3 ≠ 1 := by
  intro h; have := sqrt3_sq; rw [h] at this; norm_num at this

lemma sqrt3_ne_zero : Real.sqrt 3 ≠ 0 := by positivity

lemma rh_dist (i j : Fin 4) :
    dist (rh i) (rh j) =
      if i = j then 0 else if (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) then Real.sqrt 3 else 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [rh, d_ab, d_ac, d_ad, d_bc, d_bd, d_cd, dist_comm pb pa, dist_comm pc pa,
      dist_comm pd pa, dist_comm pc pb, dist_comm pd pb, dist_comm pd pc]

lemma rh_inj : Function.Injective rh := by
  intro i j h
  by_contra hne
  have := rh_dist i j
  rw [h, dist_self, if_neg hne] at this
  split_ifs at this
  · exact sqrt3_ne_zero this.symm
  · norm_num at this

/-- The first question has a negative answer for $n = 4$: two unit equilateral triangles
glued along an edge (a rhombus with angles $60°$ and $120°$) have only one rare distance.
The unit distance occurs $5 > 4$ times and the long diagonal $\sqrt{3}$ occurs once. -/
theorem exists_four_points_one_rare_distance :
    ∃ A : Finset Plane, A.card = 4 ∧ (rareDistances A).card < 2 := by
  refine ⟨univ.map ⟨rh, rh_inj⟩, by simp, ?_⟩
  have hsub : rareDistances (univ.map ⟨rh, rh_inj⟩) ⊆ {Real.sqrt 3} := by
    intro d hd
    simp only [rareDistances, distances, mem_filter, mem_image, mem_offDiag] at hd
    obtain ⟨⟨⟨x, y⟩, ⟨hx, hy, hxy⟩, rfl⟩, hm⟩ := hd
    simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    have hij : i ≠ j := fun h => hxy (h ▸ rfl)
    simp only [rh_dist, if_neg hij] at hm ⊢
    split_ifs with h
    · simp
    · -- the unit distance occurs `5 > 4` times, so it is not rare
      exfalso
      rw [if_neg h] at hm
      have : (((univ.map ⟨rh, rh_inj⟩) ×ˢ (univ.map ⟨rh, rh_inj⟩)).filter
          (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)) =
          ((univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 ≠ p.2 ∧
            ¬ ((p.1 = 0 ∧ p.2 = 3) ∨ (p.1 = 3 ∧ p.2 = 0)))).map
            ⟨fun p => (rh p.1, rh p.2), fun p q h => by
              simp only [Prod.mk.injEq] at h; exact Prod.ext (rh_inj h.1) (rh_inj h.2)⟩ := by
        ext ⟨x, y⟩
        simp only [mem_filter, mem_product, mem_map, mem_univ, true_and,
          Function.Embedding.coeFn_mk, Prod.exists]
        constructor
        · rintro ⟨⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩, hne, hd⟩
          refine ⟨a, b, ⟨fun h => hne (h ▸ rfl), ?_⟩, rfl⟩
          intro hc
          have hab : a ≠ b := fun h => hne (h ▸ rfl)
          rw [rh_dist, if_neg hab, if_pos hc] at hd
          exact sqrt3_ne_one hd
        · rintro ⟨a, b, ⟨hab, hc⟩, hpair⟩
          cases hpair
          refine ⟨⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩, fun h => hab (rh_inj h), ?_⟩
          rw [rh_dist, if_neg hab, if_neg hc]
      simp only [distMult, this, card_map] at hm
      revert hm
      decide
  calc (rareDistances _).card ≤ ({Real.sqrt 3} : Finset ℝ).card := card_le_card hsub
    _ < 2 := by simp

/-- Consequently, the first question fails if $n \ge 5$ is weakened to $n \ge 4$. -/
theorem not_forall_four_le :
    ¬ ∀ A : Finset Plane, 4 ≤ A.card → 2 ≤ (rareDistances A).card := by
  intro h
  obtain ⟨A, hA, hlt⟩ := exists_four_points_one_rare_distance
  have := h A hA.ge
  omega

/-- The PR's count of unordered pairs at distance `d`. -/
noncomputable def distanceMultiplicity (P : Finset Plane) (d : ℝ) : ℕ :=
  (P.offDiag.filter fun p => dist p.1 p.2 = d).card / 2

/-- The PR's set of distances occurring between one and `P.card` unordered pairs. -/
noncomputable def lowMultiplicityDistances (P : Finset Plane) : Set ℝ :=
  {d | 0 < distanceMultiplicity P d ∧ distanceMultiplicity P d ≤ P.card}

lemma distMult_eq (P : Finset Plane) (d : ℝ) :
    distMult P d = distanceMultiplicity P d := by
  unfold distMult distanceMultiplicity
  congr 2
  ext p
  simp only [mem_filter, mem_product, mem_offDiag]
  tauto

lemma lowMultiplicityDistances_subset (P : Finset Plane) :
    lowMultiplicityDistances P ⊆ (rareDistances P : Set ℝ) := by
  intro d hd
  obtain ⟨hpos, hle⟩ := hd
  have hcard : 0 < (P.offDiag.filter fun p => dist p.1 p.2 = d).card := by
    unfold distanceMultiplicity at hpos
    omega
  obtain ⟨⟨x, y⟩, hxy⟩ := card_pos.mp hcard
  simp only [mem_filter] at hxy
  change d ∈ rareDistances P
  simp only [rareDistances, mem_filter]
  refine ⟨?_, by rwa [distMult_eq]⟩
  exact mem_image.mpr ⟨(x, y), hxy.1, hxy.2⟩

/-- The exact `four_points` statement from PR #4389. -/
theorem four_points :
    ∃ P : Finset Plane, P.card = 4 ∧ (lowMultiplicityDistances P).ncard < 2 := by
  obtain ⟨P, hP, hrare⟩ := exists_four_points_one_rare_distance
  refine ⟨P, hP, lt_of_le_of_lt ?_ hrare⟩
  calc (lowMultiplicityDistances P).ncard ≤ (rareDistances P : Set ℝ).ncard :=
      Set.ncard_le_ncard (lowMultiplicityDistances_subset P) (finite_toSet _)
    _ = (rareDistances P).card := by simp

#print axioms exists_four_points_one_rare_distance
#print axioms four_points
end Erdos132Proof
