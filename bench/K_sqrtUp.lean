import Interval64
open Interval64 Interval64.Spec
example : (Spec.sqrtUp 4591870180066957722).toNat = 4599368272914696464 := by decide +kernel
example : (Spec.sqrtUp 4614256656552045848).toNat = 4610661241675116395 := by decide +kernel
example : (Spec.sqrtUp 13838060455033744043).toNat = 9221120237041090560 := by decide +kernel
example : (Spec.sqrtUp 4562254508917369340).toNat = 4584718143433226867 := by decide +kernel
example : (Spec.sqrtUp 4742290407625326592).toNat = 4674736413212672000 := by decide +kernel
example : (Spec.sqrtUp 13827552055903212885).toNat = 9221120237041090560 := by decide +kernel
example : (Spec.sqrtUp 3).toNat = 2192046282646244523 := by decide +kernel
example : (Spec.sqrtUp 9218868437227405311).toNat = 6913025428013711360 := by decide +kernel
