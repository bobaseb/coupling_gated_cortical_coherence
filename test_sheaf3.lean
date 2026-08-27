import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

open CategoryTheory TopologicalSpace Opposite

variable {X : TopCat} (F : TopCat.Presheaf (Type 1) X)

#check TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types F
