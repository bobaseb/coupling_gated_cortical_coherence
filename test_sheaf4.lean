import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import PhysicsOfConsciousness.Phase1_Primitives

open CategoryTheory TopologicalSpace Opposite
open PhysicsOfConsciousness

variable {X : TopCat} [MeasurableSpace X] [BorelSpace X]

#check (probabilityPresheaf X).IsSheaf
#check TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types (probabilityPresheaf X)
