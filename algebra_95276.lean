import Mathlib

/- Let C be the graph of xy=1, and denote by C* the reflection of C
in the line y = 2x.  Let the equation of C* be written in the form
12x^2 + bxy + cy^2 + d = 0.

Find the product bc. -/
theorem algebra_95276 {b c d: ℝ}
    (h : ∀ x y xr yr,
    -- (xr, yr) is the reflection of (x, y) along y = 2x iff
    -- the midpoint lies on the line y = 2x and the slope of
    -- the segment (x, y) - (xr, yr) is -1/2, i.e. perpendicular
    -- to the line y = 2x with slope 2.
    (2 * ((x + xr)/2) = (y + yr)/2 ∧ (yr -y) = -1/2 * (xr-x)) →
    -- We assume that (x, y) lies on C iff (xr, yr) lies on
    -- C*
     (x * y = 1 ↔ 12 * xr ^ 2 + b * xr * yr + c * yr ^ 2 + d = 0)) :
    b * c = 84 := by
  -- This is the main part, we calculate an explicit equation which
  -- implies the equation of C*. Afterwards we just need to show that
  -- this determines the coefficients
  have imp: ∀ x y: ℝ, 12 * x ^ 2 -7 * x * y - 12 * y ^ 2 + 25 = 0 → 12 * x ^ 2 + b * x * y + c * y ^ 2 + d = 0 := by
    intros xr yr hxyr
    -- Introduce a point (x, y) which is the reflection of (xr, yr)
    let x := (-3 * xr + 4 * yr) / 5
    let y := (4 * xr + 3 * yr) / 5
    -- Show that (xr, yr) is the reflection of (x, y)
    have refl: 2 * ((x + xr)/2) = (y + yr)/2 ∧ (yr -y) = -1/2 * (xr-x):= by apply And.intro <;> ring
    have hxy: x * y = 1 := by calc
      x * y = ((-3 * xr + 4 * yr) / 5) * ((4 * xr + 3 * yr) / 5)            := by rfl
          _ = -1 / 25 * (12 * xr ^ 2 - 7 * xr * yr - 12 * yr ^ 2 + 25) + 1  := by ring
          _ = -1 / 25 * 0 + 1                                               := by rw [hxyr]
          _ = 1                                                             := by ring
    exact (h x y xr yr refl).mp hxy
  -- It is easiest so now just plug in enough values that we can recover
  -- b, c and d from the resulting linear equations
  -- Result of reflecting (1,1) along y=2x:
  have :_ := imp (1/5) (7/5) (by ring)
  -- Result of reflecting (2,1/2) along y=2x:
  have :_ := imp (-4/5) (19/10) (by ring)
  -- Result of reflecting (1/2,2) along y=2x:
  have :_ := imp (13/10) (8/5) (by ring)
  have : b = -7 := by linarith
  have : c = -12 := by linarith
  simp [*]; ring
