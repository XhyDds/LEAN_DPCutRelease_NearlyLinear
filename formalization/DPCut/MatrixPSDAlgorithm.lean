import DPCut.MatrixElimination

/-! Measurability and total correctness of the scalar PSD algorithm. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace DPCut.MatrixElimination
attribute [local instance] Classical.propDecidable

lemma measurable_option_cases_all {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] {f : A → B} {g : A × C → B}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : A × Option C => p.2.elim (f p.1) (fun c => g (p.1,c))) := by
  by_cases h : Nonempty C
  · letI : Inhabited C := Classical.inhabited_of_nonempty h
    exact measurable_option_cases hf hg
  · letI : IsEmpty C := not_nonempty_iff.mp h
    convert hf.comp (measurable_fst : Measurable (Prod.fst : A × Option C → A)) using 1
    funext p
    cases p.2 with
    | none => rfl
    | some c => exact isEmptyElim c

lemma measurable_option_map_vary {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [Inhabited B]
    {f : A × B → C} {o : A → Option B} (hf : Measurable f) (ho : Measurable o) :
    Measurable (fun a => (o a).map (fun b => f (a,b))) := by
  have h : Measurable (fun a => if o a = none then none else
      some (f (a, (o a).getD default))) :=
    Measurable.ite (ho measurableSet_option_none) measurable_const
      (measurable_some.comp (hf.comp (measurable_id.prodMk ((measurable_option_getD default).comp ho))))
  convert h using 1
  funext a; cases o a <;> simp

@[fun_prop] lemma measurable_tail (n : ℕ) : Measurable (tail (n:=n)) := by unfold tail; fun_prop
@[fun_prop] lemma measurable_row (n : ℕ) : Measurable (row (n:=n)) := by unfold row; fun_prop
@[fun_prop] lemma measurable_schur (n : ℕ) : Measurable (schur (n:=n)) := by unfold schur tail row; fun_prop
@[fun_prop] lemma measurable_prepend (n : ℕ) : Measurable (fun p : ℝ × (Fin n → ℝ) => prepend p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

lemma measurable_firstNonzero (n : ℕ) : Measurable (firstNonzero (n:=n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun r : Fin (n+1) → ℝ => firstNonzero r)
    simp only [firstNonzero]
    apply Measurable.ite (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)
      ?_ measurable_const
    have hh := (measurable_option_elim none (measurable_some.comp (measurable_of_finite Fin.succ))).comp
      (ih.comp (f := fun r : Fin (n+1) → ℝ => fun i : Fin n => r i.succ) (by fun_prop))
    convert hh using 1
    funext r
    cases h : firstNonzero (fun i : Fin n => r i.succ) <;> simp [Function.comp_def, h]

lemma measurable_psdWitness (n : ℕ) : Measurable (psdWitness (n:=n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun M : Mat (n+1) => psdWitness M)
    simp only [psdWitness]
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) measurable_const
    apply Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const)
    · have hnone : Measurable (fun M : Mat (n+1) => (psdWitness (tail M)).map (prepend 0)) := by
        apply measurable_option_map_vary (f := fun p : Mat (n+1) × (Fin n → ℝ) => prepend 0 p.2)
          (o := fun M : Mat (n+1) => psdWitness (tail M))
        · exact (measurable_prepend n).comp (measurable_const.prodMk measurable_snd)
        · exact ih.comp (measurable_tail n)
      have hsome : Measurable (fun p : Mat (n+1) × Fin n =>
          some (prepend (-(tail p.1 p.2 p.2+1)/(2*row p.1 p.2)) (Pi.single p.2 1))) := by
        apply measurable_some.comp
        apply (measurable_prepend n).comp
          (f := fun p : Mat (n+1) × Fin n => (-(tail p.1 p.2 p.2+1)/(2*row p.1 p.2), Pi.single p.2 1))
        apply Measurable.prodMk
        · apply measurable_from_prod_countable_left
          intro j
          dsimp [tail, row]
          fun_prop
        · exact (measurable_of_finite (fun j : Fin n => (Pi.single j 1 : Fin n → ℝ))).comp measurable_snd
      have hh := (measurable_option_cases_all hnone hsome).comp
        (measurable_id.prodMk ((measurable_firstNonzero n).comp (measurable_row n)))
      convert hh using 1
      funext M; cases h : firstNonzero (row M) <;> simp [h]
    · apply measurable_option_map_vary
        (f := fun p : Mat (n+1) × (Fin n → ℝ) => prepend (-(row p.1 ⬝ᵥ p.2)/p.1 0 0) p.2)
        (o := fun M : Mat (n+1) => psdWitness (schur M))
      · apply (measurable_prepend n).comp
          (f := fun p : Mat (n+1) × (Fin n → ℝ) => (-(row p.1 ⬝ᵥ p.2)/p.1 0 0,p.2))
        apply Measurable.prodMk
        · unfold row dotProduct; fun_prop
        · exact measurable_snd
      · exact ih.comp (measurable_schur n)

def symmetrize {n : ℕ} (M : Mat n) : Mat n := fun i j => (M i j + M j i)/2

lemma symmetrize_hermitian {n : ℕ} (M : Mat n) : (symmetrize M).IsHermitian := by
  ext i j; simp [Matrix.conjTranspose_apply, symmetrize, add_comm]

lemma symmetrize_eq {n : ℕ} {M : Mat n} (h : M.IsHermitian) : symmetrize M = M := by
  ext i j; rw [symmetrize, symmetric h]; ring

lemma qform_symmetrize {n : ℕ} (M : Mat n) (v : Fin n → ℝ) :
    qform (symmetrize M) v = qform M v := by
  have ht : qform Mᵀ v = qform M v := by
    unfold qform
    rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
  have hs : symmetrize M = (1/2:ℝ) • (M + Mᵀ) := by ext i j; simp [symmetrize]; ring
  rw [hs]
  simp only [qform, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add] at *
  rw [ht, smul_eq_mul]; ring

/-- Defined on every real matrix by symmetrization, so every returned witness
is valid even when the caller has not supplied a symmetry proof. -/
def totalPSD {n : ℕ} (M : Mat n) : Option (Fin n → ℝ) := psdWitness (symmetrize M)

lemma totalPSD_measurable (n : ℕ) : Measurable (totalPSD (n:=n)) :=
  (measurable_psdWitness n).comp (by unfold symmetrize; fun_prop)

lemma totalPSD_negative {n : ℕ} (M : Mat n) (v : Fin n → ℝ) (h : totalPSD M = some v) :
    v ⬝ᵥ (M *ᵥ v) < 0 := by
  have hh := psdWitness_correct (symmetrize M) (symmetrize_hermitian M)
  rw [show psdWitness (symmetrize M) = some v from h] at hh
  simpa [qform_symmetrize] using hh

lemma totalPSD_none {n : ℕ} (M : Mat n) (hM : M.IsHermitian) :
    totalPSD M = none ↔ M.PosSemidef := by
  constructor
  · intro h
    have hh := psdWitness_correct M hM
    have he : psdWitness M = none := by simpa [totalPSD, symmetrize_eq hM] using h
    simpa [he] using hh
  · intro hp
    cases h : totalPSD M with
    | none => rfl
    | some v => exact False.elim ((not_lt_of_ge (hp.2 v)) (totalPSD_negative M v h))

/-- The previous external semantic interface now has a proved implementation.
Operation counts are supplied separately by the arithmetic refinement. -/
def primitives : LinearAlgebraPrimitives where
  psdWitness _ := totalPSD
  measurable_psdWitness := totalPSD_measurable
  none_iff := fun _ => totalPSD_none
  witness_negative := fun _ => totalPSD_negative

end DPCut.MatrixElimination
