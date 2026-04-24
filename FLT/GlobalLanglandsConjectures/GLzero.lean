/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer
-/
import Mathlib.Data.Int.Star
import FLT.GlobalLanglandsConjectures.GLnDefs
import FLT.NumberField.Completion.Finite
import FLT.Mathlib.NumberTheory.NumberField.FiniteAdeleRing
import FLT.QuaternionAlgebra.NumberField

/-!
# Proof of a case of the global Langlands conjectures.

Class Field Theory was one of the highlights of 19th century mathematics, linking
analysis to arithmetic of extensions of number fields with abelian Galois groups.
In the 1960s the main results had been re-interpreted as the GL(1) case of the global
Langlands conjectures. The general global Langlands conjectures are for GL(n) for any natural
number n, and work over any number field or global function field. Much is known in the function
field case (Lafforgue got a Fields Medal for his work on the topic), but the general number
field case remains largely open even today. For example we have very few results if the
base number field is not totally real or CM. For simplicity, let us stick to GL(n)/Q.

In 1993 Wiles announced his proof of the modularity of semistable elliptic curves over the
rationals. The result gave us a way of constructing automorphic forms from Galois representations;
refinements of the work by Taylor and others over the next decade led to a profound understanding
of the "holomorphic" or "odd" part of global Langlands functoriality for GL(2) over the rationals.
Wiles' work used class field theory (in the form of global Tate duality) crucially in a
central proof that a deformation ring R was isomorphic to a Hecke algebra T.

The fact that Wiles needed the theory for GL(1) to make progress in the GL(2) case,
is surely evidence that at the end of the day the proof for GL(n) is going to be by induction on n.
We will thus attempt to prove the global Langlands conjectures for GL(0).

## Structure of the proof

We will deduce the global Langlands conjectures for GL(0) from a far stronger theorem,
called the *classification theorem for automorphic representations for GL(0) over Q*.
This theorem gives a *canonical isomorphism* between the space of automorphic representations
and the complex numbers. Except in Lean we're not allowed to say "canonical" so instead
our "theorem" is a *definition* of a bijection.

## TODO

State them first.

-/

namespace AutomorphicForm

def GLn.Weight.IsTrivial {n : ℕ} (ρ : Weight n) : Prop := ρ.w.rho = 1

open GLn Manifold

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GL0

variable (ρ : Weight 0)

/-- Make an automorphic form for GL₀/ℚ from a complex number -/
def ofComplex (c : ℂ) : AutomorphicFormForGLnOverQ 0 ρ := {
    toFun := fun _ => c,
    is_smooth := {
      continuous := by continuity
      loc_cst := fun _ => IsLocallyConstant.const c
      smooth := by simp [contMDiff_const]
    }
    is_periodic := by simp
    is_slowly_increasing x := ⟨‖c‖, 0, by simp⟩
    is_finite_cod := by
      intro x
      -- For n=0, GL(Fin 0) ℝ is a point (Subsingleton).
      -- The Lie algebra is trivial, so UEA ≅ ℂ, Z ≅ ℂ,
      -- and any quotient of Z is finite-dimensional.
      haveI : Subsingleton (GL (Fin 0) ℝ) := inferInstance
      -- Step 1: LeftInvariantDerivation is unique (trivial).
      -- Every smooth function on a one-point space is constant,
      -- and derivations kill constants (algebraMap).
      haveI : Unique (LeftInvariantDerivation 𝓘(ℝ, Matrix (Fin 0) (Fin 0) ℝ) (GL (Fin 0) ℝ)) := by
        refine ⟨⟨0⟩, fun a => ?_⟩
        ext f g
        have hf : f = algebraMap ℝ _ (f 1) := by
          ext ⟨y, hy⟩
          simp [Algebra.algebraMap_eq_smul_one]
          congr 1
          exact Subsingleton.elim _ _
        rw [hf]
        have h := a.toDerivation.map_algebraMap (f 1)
        change (a.toDerivation (algebraMap ℝ _ (f 1))) g =
          (0 : C^⊤⟮𝓘(ℝ, Matrix (Fin 0) (Fin 0) ℝ),
            GL (Fin 0) ℝ; 𝓘(ℝ, ℝ), ℝ⟯) g
        simp [h]
      -- LeftInvariantDerivation is Unique, so UEA(0) = ℂ.
      -- algebraMap ℂ → Alg is surjective, Z is f.d.
      let ret : Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)
          →ₐ[ℂ] ℂ := UniversalEnvelopingAlgebra.lift ℂ 0
      have h_section : ∀ a, algebraMap ℂ
          (Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ))
          (ret a) = a := by
        intro a
        letI : Ring
            (Alg (GL (Fin 0) ℝ)
              (Matrix (Fin 0) (Fin 0) ℝ)) :=
          inferInstanceAs
            (Ring (UniversalEnvelopingAlgebra ℂ _))
        let A :=
          Alg (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)
        have key : (Algebra.ofId ℂ A).comp ret =
            AlgHom.id ℂ A := by
          change (Algebra.ofId ℂ A).comp ret =
            AlgHom.id ℂ A
          have h1 : (Algebra.ofId ℂ A).comp ret =
            (UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A))
              ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).symm
                ((Algebra.ofId ℂ A).comp ret)) :=
            ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).apply_symm_apply _).symm
          have h2 : AlgHom.id ℂ A =
            (UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A))
              ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).symm
                (AlgHom.id ℂ A)) :=
            ((UniversalEnvelopingAlgebra.lift (R := ℂ) (A := A)).apply_symm_apply _).symm
          rw [h1, h2]; congr 1; ext l
          simp [show l = 0 from Subsingleton.elim _ _]
        have h := AlgHom.congr_fun key a
        simp only [AlgHom.comp_apply,
          Algebra.ofId_apply] at h
        exact h
      have hAlg_surj : Function.Surjective
          (algebraMap ℂ (Alg (GL (Fin 0) ℝ)
            (Matrix (Fin 0) (Fin 0) ℝ))) :=
        fun a => ⟨ret a, h_section a⟩
      let toZ : ℂ →ₗ[ℂ]
          ↥(Z (GL (Fin 0) ℝ)
            (Matrix (Fin 0) (Fin 0) ℝ)) :=
        { toFun := fun z => ⟨algebraMap ℂ _ z, Subalgebra.algebraMap_mem _ z⟩
          map_add' := by intro a b; ext; simp [map_add]
          map_smul' := by intro a b; ext; simp [Algebra.smul_def] }
      have htoZ_surj : Function.Surjective toZ := by
        intro ⟨a, ha⟩
        obtain ⟨z, hz⟩ := hAlg_surj a
        exact ⟨z, by ext; exact hz⟩
      haveI : Module.Finite ℂ ↥(Z (GL (Fin 0) ℝ) (Matrix (Fin 0) (Fin 0) ℝ)) :=
        Module.Finite.of_surjective toZ htoZ_surj
      exact Module.Finite.quotient _ _
    has_finite_level := by
      let U : Subgroup (GL (Fin 0) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) := {
        carrier := {1},
        one_mem' := by simp,
        mul_mem' := by simp
        inv_mem' := by simp
      }
      apply Exists.intro U
      exact {
          is_open := by
            convert isOpen_univ
            ext x
            simp [show x = 1 from Subsingleton.elim x 1]
          is_compact := by aesop
          finite_level := by simp
      }
  }

-- the weakest form of the classification theorem
noncomputable def classification : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ := {
  toFun := fun f ↦ f 1
  invFun := fun c ↦ ofComplex ρ c
  left_inv := by
    rw [Function.LeftInverse]
    simp only [ofComplex]
    intro x
    have h: x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    simp_rw [← h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]
}

end GL0

/-! ## Infrastructure for has_finite_level (general n)

We construct GL_n(integralAdeles) as an open compact subgroup of GL_n(FiniteAdeleRing ℤ ℚ).
This requires proving that each adic completion integer ring of ℤ has finite residue field
and is compact, lifting the NumberField machinery to the ℤ/ℚ setting.
-/

section has_finite_level_helpers

open IsDedekindDomain NumberField IsLocalRing FiniteAdeleRing

section IntAdeles
variable (v : HeightOneSpectrum ℤ)

instance : Finite (ResidueField (v.adicCompletionIntegers ℚ)) := by
  apply (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField ℚ v).toEquiv.finite_iff.mp
  exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot

open scoped Valued in
instance : Finite (𝓀[v.adicCompletion ℚ]) :=
  inferInstanceAs (Finite (ResidueField (v.adicCompletionIntegers ℚ)))

instance : CompactSpace (v.adicCompletionIntegers ℚ) :=
  Valued.WithZeroMulInt.integer_compactSpace (v.adicCompletion ℚ) inferInstance

end IntAdeles

instance : T2Space (FiniteAdeleRing ℤ ℚ) :=
  inferInstanceAs (T2Space (RestrictedProduct _ _ _))

instance : CompactSpace (integralAdeles ℤ ℚ) :=
  isCompact_iff_compactSpace.1 <|
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

private lemma isOpen_integralAdeles_Int :
    IsOpen (integralAdeles ℤ ℚ : Set (FiniteAdeleRing ℤ ℚ)) := by
  suffices h : (integralAdeles ℤ ℚ : Set (FiniteAdeleRing ℤ ℚ)) =
    {f | ∀ i, (f : FiniteAdeleRing ℤ ℚ) i ∈
      (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) i} from
    h ▸ RestrictedProduct.isOpen_forall_mem (fun v => by
      have : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) = {x | Valued.v x ≤ 1} := by
        ext x; simp only [SetLike.mem_coe]; rfl
      rw [this]; exact Valued.isOpen_closedBall _ one_ne_zero)
  ext x; simp only [Set.mem_setOf_eq, SetLike.mem_coe]
  exact RestrictedProduct.mem_structureSubring_iff

private lemma isCompact_integralAdeles_Int :
    IsCompact (integralAdeles ℤ ℚ : Set (FiniteAdeleRing ℤ ℚ)) :=
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

private noncomputable def GLn_fullLevel (n : ℕ) :
    Subgroup (GL (Fin n) (FiniteAdeleRing ℤ ℚ)) :=
  MonoidHom.range (Units.map (RingHom.mapMatrix (integralAdeles ℤ ℚ).subtype).toMonoidHom)

private lemma GLn_fullLevel_carrier_eq (n : ℕ) :
    (GLn_fullLevel n).carrier =
    (((integralAdeles ℤ ℚ).matrix (n := Fin n)).toSubmonoid.units : Set _) := by
  ext x
  simp only [Subgroup.mem_carrier, SetLike.mem_coe, GLn_fullLevel]
  constructor
  · rintro ⟨y, hy⟩
    rw [Submonoid.mem_units_iff]
    exact ⟨fun i j => by rw [← hy]; exact (y.val i j).prop,
           fun i j => by rw [← hy]; simp only [Units.coe_map_inv]; exact (y⁻¹.val i j).prop⟩
  · intro hx
    rw [Submonoid.mem_units_iff] at hx
    obtain ⟨hval, hinv⟩ := hx
    let M : Matrix (Fin n) (Fin n) (integralAdeles ℤ ℚ) :=
      Matrix.of fun i j => ⟨x.val i j, hval i j⟩
    let Minv : Matrix (Fin n) (Fin n) (integralAdeles ℤ ℚ) :=
      Matrix.of fun i j => ⟨x.inv i j, hinv i j⟩
    have hMMinv : M * Minv = 1 := by
      have hinj : Function.Injective (RingHom.mapMatrix (integralAdeles ℤ ℚ).subtype :
        Matrix (Fin n) (Fin n) _ → Matrix (Fin n) (Fin n) _) := by
        intro a b h; funext i j
        exact Subtype.val_injective (congr_fun (congr_fun h i) j)
      apply hinj
      simp only [map_mul, map_one, RingHom.mapMatrix_apply, Matrix.map_apply, 
        Subring.coe_subtype, M, Minv, Matrix.of_apply]
      exact x.val_inv
    have hMinvM : Minv * M = 1 := mul_eq_one_comm.mp hMMinv
    exact ⟨⟨M, Minv, hMMinv, hMinvM⟩, Units.ext (by
      ext i j; simp [M, Matrix.map_apply])⟩

private theorem GLn_fullLevel_isOpen (n : ℕ) : IsOpen (GLn_fullLevel n).carrier :=
  GLn_fullLevel_carrier_eq n ▸ Submonoid.isOpen_units isOpen_integralAdeles_Int.matrix

private theorem GLn_fullLevel_isCompact (n : ℕ) : IsCompact (GLn_fullLevel n).carrier :=
  GLn_fullLevel_carrier_eq n ▸ Submonoid.units_isCompact isCompact_integralAdeles_Int.matrix

end has_finite_level_helpers

namespace GLn

-- Let's write down an inverse
-- For general n, it will only work for ρ the trivial representation, but we didn't
-- define the trivial representation yet.
-- Some of the other fields will work for all n.
def ofComplex (z : ℂ) {n : ℕ} (ρ : Weight n) (hρ : ρ.IsTrivial) :
    AutomorphicFormForGLnOverQ n ρ where
      toFun _ := z
      is_smooth := {
        continuous := by continuity
        loc_cst := fun _ => IsLocallyConstant.const z
        smooth := by simp [contMDiff_const]
      }
      is_periodic := by simp
      is_slowly_increasing x := ⟨‖z‖, 0, by simp⟩
      is_finite_cod := sorry -- needs a better name
      has_finite_level := ⟨GLn_fullLevel n, {
        is_open := GLn_fullLevel_isOpen n
        is_compact := GLn_fullLevel_isCompact n
        finite_level := fun _ _ _ => rfl
      }⟩

-- no idea why it's not computable
noncomputable def classification (ρ : Weight 0) : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ where
  toFun f := f 1
  invFun z := ofComplex z ρ (by
    unfold Weight.IsTrivial
    ext g
    rw [show g = 1 from Subsingleton.elim g 1, map_one, map_one])
  left_inv := by
    rw [Function.LeftInverse]
    simp only [ofComplex]
    intro x
    have h : x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    simp_rw [← h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]

-- Can this be beefed up to an isomorphism of complex
-- vector spaces?

end GLn

end AutomorphicForm
