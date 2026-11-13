import BoundedRefunds
open ResourceObservation
example : BoundedUniversalAgreement (-2) 1 3 (IntWindow (-2) 3) (IntWindow 1 3) :=
  shifted_windows_suffice (-2) 1 3
