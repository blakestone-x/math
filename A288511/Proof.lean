import Recurrence

#print axioms Kimberling288511.rotation
#print axioms Kimberling288511.rewrite_shape
#print axioms Kimberling288511.word_shape
#print axioms Kimberling288511.literal_numeric_bridge
#print axioms Kimberling288511.recurrence_certificate
#print axioms Kimberling288511.literal_recurrence
#print axioms Kimberling288511.all_lengths

example (n : ℕ) : ((Kimberling288511.word n).length : ℤ) =
    Kimberling288511.source n := Kimberling288511.all_lengths n
