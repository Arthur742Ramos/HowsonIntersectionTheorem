import GraphCoveringTheory.KuroshCoverLocal

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

theorem test_coverPathValue_rawTree {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H) a) :
    coverPathValue G H (rawTreePathMap G H p) = 1 := by
  induction p with
  | nil =>
      simpa [rawTreePathMap] using
        (coverPathValue_nil G H
          (a := rawBassSerreOrbitRoot G H))
  | @cons b c p e ih =>
      rw [rawTreePathMap_cons_raw]
      cases e with
      | mk e he =>
          cases e with
          | inl f =>
              rw [coverPathValue_pos G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_pos G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one
          | inr f =>
              rw [coverPathValue_neg G H (rawTreePathMap G H p) f]
              rw [ih]
              have hloop := quotientEdgeLoop_tree_neg G H f he
              have hloop' :
                  quotientEdgeLoop G H (coverBaseEdge G H f).2.2 = 𝟙 _ := by
                change quotientEdgeLoop G H f = 𝟙 _
                exact hloop
              simp only [coverEdgeLetter]
              rw [hloop']
              simpa using (treeKuroshFreeInclusion G H).map_one

end GraphCoveringTheory.Kurosh
