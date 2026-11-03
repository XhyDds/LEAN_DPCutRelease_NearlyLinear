import DPCut.TypedMachineBudgetSound
import DPCut.WitnessNormalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.TypedMachine

abbrev batchType (n k : ℕ) : ValueType := .array k (.array n .real)
abbrev witnessType (n : ℕ) : ValueType := .pair .boolean (weightType n)

def edgeTerm {Γ : List ValueType} {n : ℕ} (w : Term Γ (weightType n)) (e : Edge n) : Term Γ .real :=
  w.at (Fintype.equivFin (Edge n) e)

def weightTerms {Γ : List ValueType} {n : ℕ} (values : Edge n → Term Γ .real) : Term Γ (weightType n) :=
  .array (fun i => values ((Fintype.equivFin (Edge n)).symm i))

def zeroWeights {Γ : List ValueType} (n : ℕ) : Term Γ (weightType n) := .array (fun _ => 0)
def oneWeights {Γ : List ValueType} (n : ℕ) : Term Γ (weightType n) := .array (fun _ => 1)

def addWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm a e+edgeTerm b e)

def subWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm a e-edgeTerm b e)

def productWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) : Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm a e*edgeTerm b e)

def pairingTerm {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) : Term Γ .real :=
  .sum (productWeights a b)

def massTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) : Term Γ .real := .sum a

def l1Term {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) : Term Γ .real :=
  .sum (weightTerms (fun e => .realUnary .abs (edgeTerm a e)))

def allZero {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) : Term Γ .boolean :=
  .realCompare .eq (l1Term a) 0

def activeMaximumTerm {Γ : List ValueType} {n : ℕ} (r g : Term Γ (weightType n)) : Term Γ .real :=
  .maximum (weightTerms (fun e => .select (.realCompare .lt 0 (edgeTerm r e)) (edgeTerm g e) 0))

def normalizeTerm {Γ : List ValueType} {n : ℕ} (r g : Term Γ (weightType n)) (maximum : Term Γ .real) :
    Term Γ (weightType n) :=
  weightTerms (fun e => edgeTerm r e*edgeTerm g e/maximum)

def rawWitnessTerm {Γ : List ValueType} (n k : ℕ) (z : Term Γ (batchType n k)) : Term Γ (weightType n) :=
  weightTerms (fun e =>
    (.sum (.array (fun j : Fin k =>
      let difference := (z.at j).at e.val.1-(z.at j).at e.val.2
      difference*difference/4)))/(.cast (.natural k)))

def clippedWitnessTerm {Γ : List ValueType} (n k : ℕ) (z : Term Γ (batchType n k)) : Term Γ (weightType n) :=
  weightTerms (fun e => .realBinary .min (edgeTerm (rawWitnessTerm n k z) e/2) 1)

def batchTransformTerm {Γ : List ValueType} (n k : ℕ) (L : Term Γ (matrixType n))
    (z : Term Γ (.array (k*n) .real)) : Term Γ (batchType n k) :=
  .array (fun j : Fin k => .array (fun i : Fin n =>
    .sum (.array (fun l : Fin n => (L.at i).at l*z.at (finProdFinEquiv (j,l))))))

def noWitness {Γ : List ValueType} (n : ℕ) : Term Γ (witnessType n) :=
  .pair (.boolean false) (zeroWeights n)

def decodeWitness {n : ℕ} (r : (witnessType n).Value) : Option (Weights n) :=
  if r.1 then some (decodeWeights r.2) else none

@[simp] theorem eval_edgeTerm {Γ : List ValueType} {n : ℕ} (w : Term Γ (weightType n)) (e : Edge n)
    (s : Environment Γ) : (edgeTerm w e).eval s = decodeWeights (w.eval s) e := by
  simp [edgeTerm, decodeWeights]

@[simp] theorem eval_weightTerms {Γ : List ValueType} {n : ℕ} (values : Edge n → Term Γ .real)
    (s : Environment Γ) :
    decodeWeights ((weightTerms values).eval s) = fun e => (values e).eval s := by
  funext e
  simp [weightTerms, decodeWeights, Term.eval]

@[simp] theorem eval_zeroWeights {Γ : List ValueType} (n : ℕ) (s : Environment Γ) :
    decodeWeights ((zeroWeights n).eval s) = 0 := by
  funext e
  norm_num [zeroWeights, decodeWeights, Term.eval]

@[simp] theorem eval_oneWeights {Γ : List ValueType} (n : ℕ) (s : Environment Γ) :
    decodeWeights ((oneWeights n).eval s) = 1 := by
  funext e
  norm_num [oneWeights, decodeWeights, Term.eval]

@[simp] theorem eval_addWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((addWeights a b).eval s) = decodeWeights (a.eval s)+decodeWeights (b.eval s) := by
  simp [addWeights, Term.eval, RealBinary.eval, Pi.add_def]

@[simp] theorem eval_subWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((subWeights a b).eval s) = decodeWeights (a.eval s)-decodeWeights (b.eval s) := by
  simp [subWeights, Term.eval, RealBinary.eval, Pi.sub_def]

@[simp] theorem eval_productWeights {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) (s : Environment Γ) :
    decodeWeights ((productWeights a b).eval s) = hadamard (decodeWeights (a.eval s)) (decodeWeights (b.eval s)) := by
  simp [productWeights, Term.eval, RealBinary.eval, hadamard]
  rfl

theorem eval_sumWeights {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) (s : Environment Γ) :
    (.sum a : Term Γ .real).eval s = mass (decodeWeights (a.eval s)) := by
  exact ((Fintype.equivFin (Edge n)).sum_comp (a.eval s)).symm

@[simp] theorem eval_pairingTerm {Γ : List ValueType} {n : ℕ} (a b : Term Γ (weightType n)) (s : Environment Γ) :
    (pairingTerm a b).eval s = pairing (decodeWeights (a.eval s)) (decodeWeights (b.eval s)) := by
  rw [pairingTerm, eval_sumWeights, eval_productWeights]
  rfl

@[simp] theorem eval_massTerm {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) (s : Environment Γ) :
    (massTerm a).eval s = mass (decodeWeights (a.eval s)) := eval_sumWeights _ _

@[simp] theorem eval_l1Term {Γ : List ValueType} {n : ℕ} (a : Term Γ (weightType n)) (s : Environment Γ) :
    (l1Term a).eval s = l1 (decodeWeights (a.eval s)) := by
  rw [l1Term, eval_sumWeights, eval_weightTerms]
  simp [Term.eval, RealUnary.eval, mass, l1]

@[simp] theorem eval_rawWitnessTerm {Γ : List ValueType} (n k : ℕ) (z : Term Γ (batchType n k)) (s : Environment Γ) :
    decodeWeights ((rawWitnessTerm n k z).eval s) = rawWitness (z.eval s) := by
  rw [rawWitnessTerm, eval_weightTerms]
  funext e
  simp [Term.eval, rawWitness, RealBinary.eval, pow_two]

@[simp] theorem eval_clippedWitnessTerm {Γ : List ValueType} (n k : ℕ) (z : Term Γ (batchType n k)) (s : Environment Γ) :
    decodeWeights ((clippedWitnessTerm n k z).eval s) = clippedWitness (z.eval s) := by
  rw [clippedWitnessTerm, eval_weightTerms]
  funext e
  have hr := congrFun (eval_rawWitnessTerm n k z s) e
  simpa [Term.eval, RealBinary.eval, clippedWitness] using congrArg (fun x => min (x/2) 1) hr

@[simp] theorem eval_batchTransformTerm {Γ : List ValueType} (n k : ℕ) (L : Term Γ (matrixType n))
    (z : Term Γ (.array (k*n) .real)) (s : Environment Γ) :
    (batchTransformTerm n k L z).eval s = fun j =>
      Matrix.mulVec (L.eval s) (fun l => z.eval s (finProdFinEquiv (j,l))) := by
  funext j i
  simp [batchTransformTerm, Term.eval, RealBinary.eval, Matrix.mulVec, dotProduct]

end DPCut.TypedMachine
