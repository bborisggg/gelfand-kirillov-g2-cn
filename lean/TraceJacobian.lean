import MatrixSymbols

/-! An eight-dimensional transverse slice for the pair of traceless matrices.
At the specified integer point the Jacobian of the eight trace generators
has determinant −288. The proof also supplies a denominator-cleared inverse
to its differential over any commutative ring. -/
namespace TraceJacobian
open Lean.Grind MatrixSymbols
set_option maxHeartbeats 10000000
set_option maxRecDepth 16000

structure Tangent (R : Type) where
  x : R
  y : R
  u : R
  v : R
  c : R
  d : R
  g : R
  h : R

structure Traces (R : Type) where
  xx : R
  xy : R
  yy : R
  xxx : R
  xxy : R
  xyy : R
  yyy : R
  xxyy : R

variable {R : Type} [CommRing R]

def add (p q : Mat R) : Mat R :=
  ⟨p.a+q.a, p.b+q.b, p.c+q.c, p.d+q.d, p.e+q.e, p.f+q.f,
   p.g+q.g, p.h+q.h, p.i+q.i⟩

/-- Constant and linear coefficients of a matrix over R[ε]/(ε²). -/
structure FirstOrder (R : Type) where
  val : Mat R
  lin : Mat R

def prod (p q : FirstOrder R) : FirstOrder R :=
  ⟨mul p.val q.val, add (mul p.lin q.val) (mul p.val q.lin)⟩

/-- The tangent slice has X diagonal, and the (1,2),(2,3) entries of Y
fixed at 1. The base point is X=diag(0,1,-1), Y the cyclic permutation. -/
def coordinates (s : Tangent R) : FirstOrder R × FirstOrder R :=
  (⟨⟨0,0,0, 0,1,0, 0,0,-1⟩, ⟨s.x,0,0, 0,s.y,0, 0,0,-s.x-s.y⟩⟩,
   ⟨⟨0,1,0, 0,0,1, 1,0,0⟩, ⟨s.u,0,s.c, s.d,s.v,0, s.g,s.h,-s.u-s.v⟩⟩)

def differential (s : Tangent R) : Traces R :=
  let (X,Y) := coordinates s
  let X2 := prod X X
  let Y2 := prod Y Y
  ⟨tr X2.lin, tr (prod X Y).lin, tr Y2.lin, tr (prod X2 X).lin,
   tr (prod X2 Y).lin, tr (prod X Y2).lin, tr (prod Y2 Y).lin, tr (prod X2 Y2).lin⟩

private def linearForm (s : Tangent R) : Traces R :=
  ⟨2*s.x+4*s.y, s.u+2*s.v, 2*s.c+2*s.d+2*s.h, -3*s.x,
   -s.u, -s.c+s.d, 3*s.g, s.c+s.d+2*s.h⟩

theorem trace_linearization (s : Tangent R) : differential s = linearForm s := by
  simp only [differential, coordinates, linearForm, tr, prod, add, mul, Traces.mk.injEq]
  repeat' constructor
  all_goals grind

def decode (t : Traces R) : Tangent R :=
  ⟨-4*t.xxx, 3*t.xx+2*t.xxx, -12*t.xxy, 6*t.xy+6*t.xxy,
   6*t.yy-6*t.xyy-6*t.xxyy, 6*t.yy+6*t.xyy-6*t.xxyy,
   4*t.yyy, -6*t.yy+12*t.xxyy⟩

theorem left_inverse_cleared (s : Tangent R) : decode (differential s) =
    ⟨12*s.x,12*s.y,12*s.u,12*s.v,12*s.c,12*s.d,12*s.g,12*s.h⟩ := by
  rw [trace_linearization]
  simp only [decode, linearForm, Tangent.mk.injEq]
  repeat' constructor
  all_goals grind

theorem right_inverse_cleared (t : Traces R) : differential (decode t) =
    ⟨12*t.xx,12*t.xy,12*t.yy,12*t.xxx,12*t.xxy,12*t.xyy,12*t.yyy,12*t.xxyy⟩ := by
  rw [trace_linearization]
  simp only [decode, linearForm, Traces.mk.injEq]
  repeat' constructor
  all_goals grind

private def values (t : Traces Int) : List Int :=
  [t.xx, t.xy, t.yy, t.xxx, t.xxy, t.xyy, t.yyy, t.xxyy]

private def basis (j : Nat) : Tangent Int :=
  let v (i : Nat) : Int := if i=j then 1 else 0
  ⟨v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7⟩

/-- Rows use the trace order in Traces; columns use the coordinate order
in Tangent. Both are obtained by taking derivatives of the matrix words. -/
def jacobian : List (List Int) :=
  (List.range 8).map fun i => (List.range 8).map fun j =>
    (values (differential (basis j))).getD i 0

/-- First-row Laplace expansion including the determinant of the empty matrix. -/
def determinant : Nat → List (List Int) → Int
  | 0, _ => 1
  | _+1, [] => 0
  | n+1, row::rows =>
    row.zipIdx.foldl (fun acc (c,j) => if c=0 then acc else
      acc + (if j%2=0 then c else -c) * determinant n (rows.map fun r => r.eraseIdx j)) 0

theorem jacobian_minor : determinant 8 jacobian = -288 := by
  decide +kernel

end TraceJacobian
