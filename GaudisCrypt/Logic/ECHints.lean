import Lean.LabelAttribute

/-!
# EC's hint database `random`

    hint exact random : dhkey_ll.

EasyCrypt closes the losslessness of a sampling with the lemmas of its hint database `random`
(`dbool_ll`, a theory's `dhkey_ll`, …).  Here the label attribute `ec_random`: a lemma
`is_lossless d` tagged with it is what `islossless` (`Logic/PHoareRnd.lean`) closes a sampling
from `d` with.  EC's `hint exact random : l.` is `attribute [ec_random] l`.
-/

/-- EC's hint database `random`: lemmas `is_lossless d`, for `islossless` on a sampling. -/
register_label_attr ec_random
