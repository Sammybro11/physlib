/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/
module

public import Physlib.Optics.Frequency
/-!

# Wavelength

In this module we define the type `Wavelength`, corresponding to the wavelength of a wave
carrying the dimension of length, and relate it to the type `Frequency` through the
propagation speed of the wave via the relation `c = λ * ν`.

## i. Overview

The type `Wavelength` is `WithDim L𝓭 ℝ≥0`, i.e., a nonnegative real number tagged with
the dimension of length.

For a wave of frequency `ν > 0` propagating at a speed `c` (e.g. the speed of light),
the associated wavelength is `λ = c / ν`, and conversely a wave of wavelength `λ > 0`
has frequency `ν = c / λ`. These two constructions are inverse to one another.

## ii. Key results

- `Wavelength` : The type of wavelengths of waves.
- `Wavelength.ofFrequency` : The wavelength `c / ν` associated with a positive frequency.
- `Frequency.ofWavelength` : The frequency `c / λ` associated with a positive wavelength.
- `Wavelength.ofFrequency_mul` : The relation `λ * ν = c`.
- `Frequency.ofWavelength_mul` : The relation `ν * λ = c`.
- `Wavelength.ofFrequency_ofWavelength` and `Frequency.ofWavelength_ofFrequency` : The
  two constructions are inverse to one another.

## iii. Table of contents

- A. The Wavelength type
- B. Wavelength from frequency
- C. Frequency from wavelength
- D. Round trips

## iv. References

- https://en.wikipedia.org/wiki/Wavelength

-/

@[expose] public section

open Dimension
open scoped NNReal

/-!

## A. The Wavelength type

-/

/-- The type `Wavelength` represents the distance between consecutive
corresponding points of the same phase on the wave, such as two adjacent
crests, troughs, or zero crossings, i.e. a nonnegative real number
carrying the dimension of length. -/
abbrev Wavelength : Type := WithDim L𝓭 ℝ≥0

namespace Wavelength

/-!

## B. Wavelength from frequency

-/

/-- The wavelength of a wave of frequency `ν` propagating at a speed `c`,
given by `λ = c / ν`. -/
def ofFrequency (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val) :
    Wavelength := ⟨c.val / ν.val⟩

@[simp]
lemma ofFrequency_val (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val) :
    (ofFrequency c ν hν).val = c.val / ν.val := rfl

/-- Positivity of the wavelength associated with a positive frequency and a positive
speed. -/
lemma ofFrequency_pos (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val) (ν : Frequency)
    (hν : 0 < ν.val) : 0 < (ofFrequency c ν hν).val :=
  div_pos hc hν

/-- The wavelength associated with a frequency satisfies `λ * ν = c`. -/
lemma ofFrequency_mul (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val) :
    (ofFrequency c ν hν).val * ν.val = c.val :=
  div_mul_cancel₀ c.val (ne_of_gt hν)

end Wavelength

namespace Frequency

/-!

## C. Frequency from wavelength

-/

/-- The frequency of a wave of wavelength `w` propagating at a speed `c`,
given by `ν = c / λ`. -/
def ofWavelength (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (hw : 0 < w.val) :
    Frequency := ⟨c.val / w.val⟩

@[simp]
lemma ofWavelength_val (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (hw : 0 < w.val) :
    (ofWavelength c w hw).val = c.val / w.val := rfl

/-- Positivity of the frequency associated with a positive wavelength and a positive
speed. -/
lemma ofWavelength_pos (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val) (w : Wavelength)
    (hw : 0 < w.val) : 0 < (ofWavelength c w hw).val :=
  div_pos hc hw

/-- The frequency associated with a wavelength satisfies `ν * λ = c`. -/
lemma ofWavelength_mul (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (hw : 0 < w.val) :
    (ofWavelength c w hw).val * w.val = c.val :=
  div_mul_cancel₀ c.val (ne_of_gt hw)

/-!

## D. Round trips

-/

/-- Converting a wavelength to a frequency and back recovers the wavelength. -/
@[simp]
lemma ofWavelength_ofFrequency (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val)
    (ν : Frequency) (hν : 0 < ν.val) :
    ofWavelength c (Wavelength.ofFrequency c ν hν)
      (Wavelength.ofFrequency_pos c hc ν hν) = ν := by
  ext
  show c.val / (c.val / ν.val) = ν.val
  exact div_div_cancel₀ (ne_of_gt hc)

end Frequency

namespace Wavelength

/-- Converting a frequency to a wavelength and back recovers the frequency. -/
@[simp]
lemma ofFrequency_ofWavelength (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val)
    (w : Wavelength) (hw : 0 < w.val) :
    ofFrequency c (Frequency.ofWavelength c w hw)
      (Frequency.ofWavelength_pos c hc w hw) = w := by
  ext
  show c.val / (c.val / w.val) = w.val
  exact div_div_cancel₀ (ne_of_gt hc)

end Wavelength
