/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Analysis.Calculus.Inverse
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # The inverse function theorem for manifolds
TODO: complete docstring
-/

open Function Manifold Set TopologicalSpace Topology

-- Let M and N be manifolds over (E,H) and (E',H'), respectively.
-- We don't assume smoothness, but allow any structure groupoid (which contains C¹ maps).
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
   [TopologicalSpace N] [ChartedSpace H N]
  -- TODO: relax these conditions!!
  (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
  (J : ModelWithCorners ℝ E' H) [SmoothManifoldWithCorners J N]

/-! Re-phrasing the implicit function theorem over normed spaces in categorical language,
  using (pre-)groupoids and local structomorphisms.
  This unifies e.g. the smooth and analytic categories. -/
section IFTBasic
variable {n : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] --[CompleteSpace E]
-- XXX: generalise to any field 𝕜 which is ℝ or ℂ

/-- A pregroupoid which satisfies the necessary conditions for the implicit function theorem.

Over the real or complex numbers, this includes the `C^n` and analytic pre-groupoids. -/
structure IFTPregroupoid (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] extends Pregroupoid E where
  -- If `f ∈ P` defines a homeomorphism `s → t` with inverse `g`, then `g ∈ P` also.
  -- TODO: extend docstring
  inverse : ∀ {f g s t x}, ∀ {f' : E ≃L[ℝ] E}, x ∈ s → IsOpen s → property f s →
    HasFDerivAt (𝕜 := ℝ) f f' x → InvOn g f s t → property g t

/-- The groupoid associated to an IFT pre-groupoid. -/
def IFTPregroupoid.groupoid (PG : IFTPregroupoid E) : StructureGroupoid E :=
  (PG.toPregroupoid).groupoid

/-- The pregroupoid of `C^n` functions on `E`. -/
def contDiffPregroupoidBasic : Pregroupoid E := {
  property := fun f s ↦ ContDiffOn ℝ n f s
  comp := fun {f g} {u v} hf hg _ _ _ ↦ hg.comp' hf
  id_mem := contDiffOn_id
  locality := fun _ h ↦ contDiffOn_of_locally_contDiffOn h
  congr := by intro f g u _ congr hf; exact (contDiffOn_congr congr).mpr hf
}

-- this is the key lemma I need to showing that C^n maps define a better pregroupoid
-- we need to work over ℝ or ℂ, otherwise `toLocalInverse` doesn't apply
-- FIXME: generalise to charted spaces
-- FIXME: not entirely true; I get that g is ContDiff in *some* nhd of x, might be smaller than t!
lemma Iwant [CompleteSpace E] {f g : E → E} {s t : Set E} {x : E} {f' : E ≃L[ℝ] E}
    (hinv : InvOn g f s t) (hf : ContDiffAt ℝ n f x) (hf' : HasFDerivAt (𝕜 := ℝ) f f' x)
    (hn : 1 ≤ n) : ContDiffAt ℝ n g (f x) := by
  let r := hf.to_localInverse (f' := f') hf' hn -- ContDiffAt ℝ n (hf.localInverse hf' hn) (f x)
  set g' := ContDiffAt.localInverse hf hf' hn
  have : EqOn g g' s := by
    have : InvOn g' f s t := sorry -- by construction
    -- now, should be a basic lemma
    sorry
  -- apply fderiv_congr to rewrite g' with g
  sorry

/-- If `E` is complete and `n ≥ 1`, the pregroupoid of `C^n` functions
  is an IFT pregroupoid.
  The proof relies on the mean value theorem, which is why ℝ or ℂ is required. -/
def contDiffBasicIsIFTPregroupoid [CompleteSpace E] (hn : 1 ≤ n) : IFTPregroupoid E where
  toPregroupoid := contDiffPregroupoidBasic (n := n)
  inverse := by
    intro f g s t x f' hx hs hf hf' hinv
    unfold contDiffPregroupoidBasic
    simp only
    -- Since f is cont. differentiable on s, there's a neighbourhood U of x s.t. df_x' is an isomorphism
    -- for all x'. We use this neighbourhood.
    rcases mem_nhds_iff.mp f'.nhds with ⟨t', ht, htopen, hft⟩
    let U := (fun x ↦ fderiv ℝ f x) ⁻¹' t' ∩ s
    have : IsOpen U := by
      have : ContinuousOn (fun x ↦ fderiv ℝ f x) s := sorry -- as f is contDiff on s
      apply IsOpen.inter _ hs
      refine this.isOpen_preimage (t := t') hs ?_ htopen
      sorry -- xxx: finish arguing why this is ⊆ s
    -- each fderiv ℝ f x' for x' ∈ U is an isomorphism
    --use U
    have : MapsTo f s t := sorry -- assume; check if really needed!
    have scifi : f '' U ⊆ t := sorry -- f '' U ⊆ f '' s ⊆ t: first I just showed
    have scifi2 : IsOpen (f '' U) := sorry -- need to argue harder: f is a local homeo or so
    have hinv' : InvOn g f U (f '' U) := hinv.mono (inter_subset_right _ _) scifi
    have : ∃ V ⊆ t, IsOpen V ∧ ContDiffOn ℝ n g V := by
      use f '' U
      refine ⟨scifi, scifi2, ?_⟩
      -- run the argument below with each f' := fderiv ℝ f y
      -- unclear: how to state in Lean "df_x" is an iso
      suffices ∀ y : f '' U, ContDiffAt ℝ n g y by
        exact fun y hy ↦ (this ⟨y, hy⟩).contDiffWithinAt
      intro ⟨y, hy⟩
      let x' := g y
      have eq : g y = x' := rfl
      have : f x' = y := hinv.2 (scifi hy)
      rcases hy with ⟨x'', hx''U, hx''y⟩
      have : x' ∈ U := by rw [← eq, ← hx''y, hinv.1 (mem_of_mem_inter_right hx''U)]; exact hx''U
      let f'' := fderiv ℝ f x'
      have : HasFDerivAt f f'' x'' := sorry -- standard
      -- last: upgrade f'' to an isomorphism, then can apply r
      -- exact Iwant hinv (hf.contDiffAt (hs.mem_nhds (mem_of_mem_inter_right hx''U))) this hn
      sorry
    sorry -- TODO: adjust conclusion of statement!

end IFTBasic
