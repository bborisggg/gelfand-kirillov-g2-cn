import Std

/-! A characteristic-independent reduction of every split orbit product
to its linear factors. Multiplicities are represented by repeated list entries. -/

namespace OrbitProducts
open Lean.Grind

variable {R : Type} [CommRing R]

def productAt (xs : List R) (f : R → R) : R :=
  match xs with
  | [] => 1
  | x :: tail => f x * productAt tail f

private theorem product_one (xs : List R) :
    productAt xs (fun _ => (1:R)) = 1 := by
  induction xs with
  | nil => rfl
  | cons a tail ih =>
    change 1 * productAt tail (fun _ => (1:R)) = 1
    rw [ih]
    grind

private theorem product_mul (xs : List R) (f g : R → R) :
    productAt xs (fun x => f x * g x) = productAt xs f * productAt xs g := by
  induction xs with
  | nil =>
    change (1:R) = 1 * 1
    grind
  | cons a tail ih =>
    change (f a * g a) * productAt tail (fun x => f x * g x) =
      (f a * productAt tail f) * (g a * productAt tail g)
    rw [ih]
    grind

private theorem swap_orders (xs ys : List R) (f : R → R → R) :
    productAt xs (fun x => productAt ys (fun y => f x y)) =
      productAt ys (fun y => productAt xs (fun x => f x y)) := by
  induction ys with
  | nil =>
    change productAt xs (fun _ => (1:R)) = 1
    exact product_one xs
  | cons b tail ih =>
    change productAt xs (fun x => f x b * productAt tail (fun y => f x y)) =
      productAt xs (fun x => f x b) *
        productAt tail (fun y => productAt xs (fun x => f x y))
    rw [product_mul, ih]

/-- With A(t) = t^p − t and shifts the p residues, the hypothesis
is the linear Artin–Schreier product. The conclusion calculates the norm
of any monic split polynomial, including the quartic and the sextic. -/
theorem split_orbit_product (shifts roots : List R) (t : R) (A : R → R)
    (linear : ∀ r : R, productAt shifts (fun j => t+j-r) = A t-A r) :
    productAt shifts (fun j => productAt roots (fun r => t+j-r)) =
      productAt roots (fun r => A t-A r) := by
  rw [swap_orders]
  have hf : (fun r : R => productAt shifts (fun j => t+j-r)) =
            (fun r : R => A t-A r) := funext linear
  rw [hf]

end OrbitProducts
