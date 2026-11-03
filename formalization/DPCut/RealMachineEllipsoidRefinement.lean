import DPCut.RealMachineEllipsoidStep

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

open Matrix
open scoped BigOperators RealInnerProductSpace

namespace DPCut.RealMachine.EllipsoidCode

open SDP EllipsoidMethod

def LowEq (floor : ℕ) (new old : State) : Prop :=
  ∀ address < floor, new.memory.real address = old.memory.real address

theorem low_of_floor (code : Code) (floor : ℕ) (h : code.RealWriteFloor floor) (tapes : Tapes) (s : State) :
    LowEq floor (code.execute tapes s) s :=
  Code.realWriteFloor_frame code floor h tapes s

theorem LowEq.trans {floor : ℕ} {a b c : State} (h : LowEq floor a b) (g : LowEq floor b c) : LowEq floor a c :=
  fun address ha => (h address ha).trans (g address ha)

theorem transpose_axes (m base : ℕ) (s : State) (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) (h : Matches m base s e) :
    Matrix.toEuclideanLin (axes m base s)ᵀ = LinearMap.adjoint (e.axes : _ →ₗ[ℝ] _) := by
  rw [← h.2]
  simpa only [Matrix.conjTranspose, star_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint (axes m base s)

theorem cutProgram_value (tapes : Tapes) (s : State) (m base : ℕ) (hm : 1 ≤ m)
    (e : Ellipsoid (EuclideanSpace ℝ (Fin m))) (h : Matches m base s e) (hg : normal m base s ≠ 0) :
    Matches m base ((cutProgram m base).execute tapes s)
      (e.cut (m + 1) (by exact_mod_cast Nat.succ_le_succ hm)
        (e.unitNormal (normal m base s)) (e.unitNormal_norm hg)) := by
  let a := (matVecProgram (fun i j : Fin m => matrixAddress (slot m base 1) (j,i))
    (vectorAddress (slot m base 2)) (vectorAddress (slot m base 3))).execute tapes s
  let b := (dotProgram (n := m) (vectorAddress (slot m base 3)) (vectorAddress (slot m base 3)) (slot m base 4)).execute tapes a
  let c := (writeReal (slot m base 4) (.sqrt (readReal (slot m base 4)))).execute tapes b
  let d := (arrayProgram (vectorAddress (slot m base 5)) (fun i : Fin m =>
    Expr.div (readReal (vectorAddress (slot m base 3) i)) (readReal (slot m base 4)))).execute tapes c
  let f := (matVecProgram (fun i j : Fin m => matrixAddress (slot m base 1) (i,j))
    (vectorAddress (slot m base 5)) (vectorAddress (slot m base 6))).execute tapes d
  let j := (writeReal (slot m base 10) (axialExpression m)).execute tapes f
  let k := (writeReal (slot m base 11) (transverseExpression m)).execute tapes j
  let l := (matrixMapProgram m (slot m base 7) (updateExpr m base)).execute tapes k
  let p := (mulProgram m (slot m base 1) (slot m base 7) (slot m base 9)).execute tapes l
  let q := (arrayProgram (vectorAddress (slot m base 8)) (fun i : Fin m =>
    Expr.sub (readReal (vectorAddress (slot m base 0) i))
      (.div (readReal (vectorAddress (slot m base 6) i)) (.cast (.natural (m + 2)))))).execute tapes p
  let r := (matrixMapProgram m (slot m base 1) (fun ij => readReal (matrixAddress (slot m base 9) ij))).execute tapes q
  let result := (arrayProgram (vectorAddress (slot m base 0))
    (fun i : Fin m => readReal (vectorAddress (slot m base 8) i))).execute tapes r
  have hs := stride_bounds m
  have ad (address : ℕ) (ha : address < slot m base 3) : a.memory.real address = s.memory.real address :=
    (low_of_floor _ _ (floor_matVec _ _ _ _ (fun i => (vector_range (slot m base 3) i).1)) tapes s) address ha
  have bd (address : ℕ) (ha : address ≠ slot m base 4) : b.memory.real address = a.memory.real address :=
    dotProgram_frame _ _ _ _ _ _ ha
  have cd (address : ℕ) (ha : address ≠ slot m base 4) : c.memory.real address = b.memory.real address :=
    writeReal_frame _ _ _ _ _ ha
  have dd (address : ℕ) (ha : address < slot m base 5) : d.memory.real address = c.memory.real address :=
    (low_of_floor _ _ (floor_array _ _ _ (fun i => (vector_range (slot m base 5) i).1)) tapes c) address ha
  have fd (address : ℕ) (ha : address < slot m base 6) : f.memory.real address = d.memory.real address :=
    (low_of_floor _ _ (floor_matVec _ _ _ _ (fun i => (vector_range (slot m base 6) i).1)) tapes d) address ha
  have jd (address : ℕ) (ha : address ≠ slot m base 10) : j.memory.real address = f.memory.real address :=
    writeReal_frame _ _ _ _ _ ha
  have kd (address : ℕ) (ha : address ≠ slot m base 11) : k.memory.real address = j.memory.real address :=
    writeReal_frame _ _ _ _ _ ha
  have ld (address : ℕ) (ha : address < slot m base 7) : l.memory.real address = k.memory.real address :=
    matrixMap_below _ _ _ _ _ _ ha
  have pd (address : ℕ) (ha : address < slot m base 9) : p.memory.real address = l.memory.real address := by
    have hf (entries : List (Fin m × Fin m)) :
        (mulLoop (slot m base 1) (slot m base 7) (slot m base 9) entries).RealWriteFloor (slot m base 9) := by
      induction entries with
      | nil => trivial
      | cons ij entries ih => exact ⟨floor_dot _ _ _ _ (matrix_range (slot m base 9) ij).1, ih⟩
    exact Code.realWriteFloor_frame _ _ (hf _) _ _ _ ha
  have lowk (address : ℕ) (ha : address < slot m base 3) : k.memory.real address = s.memory.real address := by
    rw [kd _ (ha.trans (slot_lt_slot m base 3 11 (by decide))).ne,
      jd _ (ha.trans (slot_lt_slot m base 3 10 (by decide))).ne,
      fd _ (ha.trans (slot_lt_slot m base 3 6 (by decide))),
      dd _ (ha.trans (slot_lt_slot m base 3 5 (by decide))),
      cd _ (ha.trans (slot_lt_slot m base 3 4 (by decide))).ne,
      bd _ (ha.trans (slot_lt_slot m base 3 4 (by decide))).ne, ad _ ha]
  have lowp (address : ℕ) (ha : address < slot m base 3) : p.memory.real address = s.memory.real address := by
    rw [pd _ (ha.trans (slot_lt_slot m base 3 9 (by decide))),
      ld _ (ha.trans (slot_lt_slot m base 3 7 (by decide))), lowk _ ha]
  have hpull : readVector m (slot m base 3) a.memory =
      (axes m base s)ᵀ *ᵥ readVector m (slot m base 2) s.memory := by
    funext i
    exact matVecProgram_value _ _ _ _ _ (vectorAddress_injective _) (by
      intro i j k
      have hi := matrix_before_slot m base 1 3 (by decide) (j,i)
      have ho := (vector_range (slot m base 3) k).1
      omega) (by
      intro i j
      have hi := vector_before_slot m base 2 3 (by decide) i
      have ho := (vector_range (slot m base 3) j).1
      omega) i
  have hpullE : WithLp.toLp 2 (readVector m (slot m base 3) a.memory) = e.pullNormal (normal m base s) := by
    rw [hpull]
    change Matrix.toEuclideanLin (axes m base s)ᵀ (normal m base s) = _
    rw [transpose_axes _ _ _ _ h]
    rfl
  have hpullc : readVector m (slot m base 3) c.memory = readVector m (slot m base 3) a.memory := by
    funext i
    have hi := vector_before_slot m base 3 4 (by decide) i
    exact (cd _ hi.ne).trans (bd _ hi.ne)
  have hnorm : c.memory.real (slot m base 4) = ‖e.pullNormal (normal m base s)‖ := by
    rw [writeReal_value]
    simp only [Expr.eval, readReal]
    have hd := dotProgram_value tapes a (vectorAddress (slot m base 3)) (vectorAddress (slot m base 3)) (slot m base 4)
      (fun i => (vector_before_slot m base 3 4 (by decide) i).ne)
      (fun i => (vector_before_slot m base 3 4 (by decide) i).ne)
    rw [hd]
    have he : (∑ i : Fin m, a.memory.real (vectorAddress (slot m base 3) i) *
        a.memory.real (vectorAddress (slot m base 3) i)) = ‖e.pullNormal (normal m base s)‖ ^ 2 := by
      rw [← hpullE]
      rw [EuclideanSpace.norm_sq_eq]
      simp [readVector, pow_two, Real.norm_eq_abs]
    rw [he, Real.sqrt_sq (norm_nonneg _)]
  have hu : WithLp.toLp 2 (readVector m (slot m base 5) d.memory) = e.unitNormal (normal m base s) := by
    have hv := arrayProgram_value tapes c (vectorAddress (slot m base 5)) (fun i : Fin m =>
      Expr.div (readReal (vectorAddress (slot m base 3) i)) (readReal (slot m base 4))) (vectorAddress_injective _)
      (by intro i j; exact (realFrame_div
        (realFrame_read _ _ (by
          have hi := vector_before_slot m base 3 5 (by decide) i
          have ho := (vector_range (slot m base 5) j).1
          omega))
        (realFrame_read _ _ (by
          have hi := slot_lt_slot m base 4 5 (by decide)
          have ho := (vector_range (slot m base 5) j).1
          omega))))
    ext i
    change d.memory.real (vectorAddress (slot m base 5) i) = _
    rw [hv i]
    simp only [Expr.eval, readReal, hnorm, Ellipsoid.unitNormal, PiLp.smul_apply, smul_eq_mul]
    have hp := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i) hpullE
    have hc := congrFun hpullc i
    simp only [PiLp.toLp_apply, readVector] at hp
    change c.memory.real (vectorAddress (slot m base 3) i) = a.memory.real (vectorAddress (slot m base 3) i) at hc
    rw [hc, hp]
    ring
  have hUk : WithLp.toLp 2 (readVector m (slot m base 5) k.memory) = e.unitNormal (normal m base s) := by
    rw [← hu]
    ext i
    have hi := vector_before_slot m base 5 6 (by decide) i
    change k.memory.real (vectorAddress (slot m base 5) i) = d.memory.real _
    rw [kd _ (hi.trans (slot_lt_slot m base 6 11 (by decide))).ne,
      jd _ (hi.trans (slot_lt_slot m base 6 10 (by decide))).ne, fd _ hi]
  have hImage : WithLp.toLp 2 (readVector m (slot m base 6) f.memory) =
      e.axes (e.unitNormal (normal m base s)) := by
    have hAd : readMatrix m (slot m base 1) d.memory = axes m base s := by
      funext i j
      have hi := matrix_before_slot m base 1 3 (by decide) (i,j)
      exact (dd _ (hi.trans (slot_lt_slot m base 3 5 (by decide)))).trans
        ((cd _ (hi.trans (slot_lt_slot m base 3 4 (by decide))).ne).trans
          ((bd _ (hi.trans (slot_lt_slot m base 3 4 (by decide))).ne).trans (ad _ hi)))
    have hv : readVector m (slot m base 6) f.memory =
        readMatrix m (slot m base 1) d.memory *ᵥ readVector m (slot m base 5) d.memory := by
      funext i
      exact matVecProgram_value _ _ _ _ _ (vectorAddress_injective _) (by
        intro i j k
        have hi := matrix_before_slot m base 1 6 (by decide) (i,j)
        have ho := (vector_range (slot m base 6) k).1
        omega) (by
        intro i j
        have hi := vector_before_slot m base 5 6 (by decide) i
        have ho := (vector_range (slot m base 6) j).1
        omega) i
    rw [hv, hAd]
    change Matrix.toEuclideanLin (axes m base s) (WithLp.toLp 2 (readVector m (slot m base 5) d.memory)) = _
    rw [hu, h.2]
    rfl
  have halpha : k.memory.real (slot m base 10) = axialRadius ((m + 1 : ℕ) : ℝ) := by
    rw [kd _ (slot_lt_slot m base 10 11 (by decide)).ne, writeReal_value]
    exact axialExpression_value _ _
  have hbeta : k.memory.real (slot m base 11) = transverseRadius ((m + 1 : ℕ) : ℝ) := by
    rw [writeReal_value]
    exact transverseExpression_value _ _
  have hB : readMatrix m (slot m base 7) l.memory =
      transverseRadius ((m + 1 : ℕ) : ℝ) • 1 +
        (axialRadius ((m + 1 : ℕ) : ℝ) - transverseRadius ((m + 1 : ℕ) : ℝ)) •
          vecMulVec (WithLp.ofLp (e.unitNormal (normal m base s))) (WithLp.ofLp (e.unitNormal (normal m base s))) := by
    have hv := matrixMap_value tapes k m (slot m base 7) (updateExpr m base) (by
      intro ij kl
      unfold updateExpr
      apply realFrame_add
      · split
        · exact realFrame_read _ _ (by have ho := matrix_before_slot m base 7 11 (by decide) kl; omega)
        · exact realFrame_rational _ _
      · apply realFrame_mul
        · exact realFrame_mul (realFrame_sub
            (realFrame_read _ _ (by have ho := matrix_before_slot m base 7 10 (by decide) kl; omega))
            (realFrame_read _ _ (by have ho := matrix_before_slot m base 7 11 (by decide) kl; omega)))
            (realFrame_read _ _ (by
              have hi := vector_before_slot m base 5 7 (by decide) ij.1
              have ho := (matrix_range (slot m base 7) kl).1
              omega))
        · exact realFrame_read _ _ (by
            have hi := vector_before_slot m base 5 7 (by decide) ij.2
            have ho := (matrix_range (slot m base 7) kl).1
            omega))
    funext i j
    rw [hv i j]
    have hui := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i) hUk
    have huj := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x j) hUk
    simp only [PiLp.toLp_apply, readVector] at hui huj
    by_cases hij : i = j <;>
      simp [updateExpr, Expr.eval, readReal, halpha, hbeta, hui, huj, hij, Matrix.one_apply, Matrix.vecMulVec] <;> ring
  have hAp : readMatrix m (slot m base 9) p.memory =
      axes m base s * readMatrix m (slot m base 7) l.memory := by
    rw [mulProgram_value _ _ _ _ _ _ (matrix_disjoint m base 1 9 (by decide)) (matrix_disjoint m base 7 9 (by decide))]
    congr 1
    funext i j
    have hi := matrix_before_slot m base 1 3 (by decide) (i,j)
    exact (ld _ (hi.trans (slot_lt_slot m base 3 7 (by decide)))).trans (lowk _ hi)
  have hCq : WithLp.toLp 2 (readVector m (slot m base 8) q.memory) =
      e.center - (1 / ((m + 2 : ℕ) : ℝ)) • e.axes (e.unitNormal (normal m base s)) := by
    have hv := arrayProgram_value tapes p (vectorAddress (slot m base 8)) (fun i : Fin m =>
      Expr.sub (readReal (vectorAddress (slot m base 0) i))
        (.div (readReal (vectorAddress (slot m base 6) i)) (.cast (.natural (m + 2)))))
      (vectorAddress_injective _) (by
        intro i j
        exact realFrame_sub (realFrame_read _ _ (by
          have hi := vector_before_slot m base 0 8 (by decide) i
          have ho := (vector_range (slot m base 8) j).1
          omega)) (realFrame_div (realFrame_read _ _ (by
            have hi := vector_before_slot m base 6 8 (by decide) i
            have ho := (vector_range (slot m base 8) j).1
            omega)) (by intro memory value; rfl)))
    ext i
    change q.memory.real (vectorAddress (slot m base 8) i) = _
    rw [hv i]
    have hc0 := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i) h.1
    have himg := congrArg (fun x : EuclideanSpace ℝ (Fin m) => x i) hImage
    simp only [center, PiLp.toLp_apply, readVector] at hc0 himg
    have hi := vector_before_slot m base 6 7 (by decide) i
    have himgP : p.memory.real (vectorAddress (slot m base 6) i) = f.memory.real (vectorAddress (slot m base 6) i) := by
      rw [pd _ (hi.trans (slot_lt_slot m base 7 9 (by decide))), ld _ hi,
        kd _ (hi.trans (slot_lt_slot m base 7 11 (by decide))).ne,
        jd _ (hi.trans (slot_lt_slot m base 7 10 (by decide))).ne]
    simp only [Expr.eval, readReal, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [lowp _ (vector_before_slot m base 0 3 (by decide) i), hc0, himgP, himg]
    ring
  have hAr : readMatrix m (slot m base 1) r.memory = readMatrix m (slot m base 9) p.memory := by
    have hv := matrixMap_value tapes q m (slot m base 1) (fun ij => readReal (matrixAddress (slot m base 9) ij))
      (fun ij kl => realFrame_read _ _ (matrix_disjoint m base 9 1 (by decide) ij kl))
    funext i j
    rw [hv i j]
    simp only [Expr.eval, readReal]
    exact arrayProgram_frame tapes p _ _ _ (by
      intro k
      have hi := (matrix_range (slot m base 9) (i,j)).1
      have ho := vector_before_slot m base 8 9 (by decide) k
      omega)
  have hCresult : center m base result = WithLp.toLp 2 (readVector m (slot m base 8) q.memory) := by
    have hv := arrayProgram_value tapes r (vectorAddress (slot m base 0)) (fun i : Fin m => readReal (vectorAddress (slot m base 8) i))
      (vectorAddress_injective _) (fun i j => realFrame_read _ _ (by
        have hi := (vector_range (slot m base 8) i).1
        have ho := vector_before_slot m base 0 8 (by decide) j
        omega))
    ext i
    change result.memory.real (vectorAddress (slot m base 0) i) = _
    rw [hv i]
    simp only [Expr.eval, readReal]
    exact matrixMap_frame tapes q m _ _ _ (by
      intro ij
      have hi := (vector_range (slot m base 8) i).1
      have ho := matrix_before_slot m base 1 8 (by decide) ij
      omega)
  have hAresult : axes m base result = readMatrix m (slot m base 1) r.memory := by
    funext i j
    exact arrayProgram_frame tapes r _ _ _ (by
      intro k
      have hi := (matrix_range (slot m base 1) (i,j)).1
      have ho := vector_before_slot m base 0 1 (by decide) k
      omega)
  change Matches m base result _
  refine ⟨?_, ?_⟩
  · rw [hCresult, hCq]
    change e.center - _ = e.center - _
    rw [map_smul]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 2
    ring
  · rw [hAresult, hAr, hAp, hB]
    have hlin : Matrix.toEuclideanLin
        (axes m base s * (transverseRadius ((m + 1 : ℕ) : ℝ) • 1 +
          (axialRadius ((m + 1 : ℕ) : ℝ) - transverseRadius ((m + 1 : ℕ) : ℝ)) •
            vecMulVec (WithLp.ofLp (e.unitNormal (normal m base s))) (WithLp.ofLp (e.unitNormal (normal m base s))))) =
        (Matrix.toEuclideanLin (axes m base s)).comp
          (axialMap (e.unitNormal (normal m base s)) (axialRadius ((m + 1 : ℕ) : ℝ)) (transverseRadius ((m + 1 : ℕ) : ℝ))) := by
      rw [axialMap_matrix]
      ext v i
      simp [Matrix.toEuclideanLin_apply, ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hlin, h.2]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl

end DPCut.RealMachine.EllipsoidCode
