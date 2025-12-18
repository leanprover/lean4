example (a b c d e : UInt8) : ((a + (b * c)) = (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec = b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt16) : ((a + (b * c)) = (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec = b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt32) : ((a + (b * c)) = (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec = b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt64) : ((a + (b * c)) = (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec = b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : USize) : ((a + (b * c)) = (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec = b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt8) : ((a + (b * c)) < (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec < b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt16) : ((a + (b * c)) < (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec < b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt32) : ((a + (b * c)) < (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec < b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt64) : ((a + (b * c)) < (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec < b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : USize) : ((a + (b * c)) < (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec < b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt8) : ((a + (b * c)) ≤ (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec ≤ b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt16) : ((a + (b * c)) ≤ (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec ≤ b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt32) : ((a + (b * c)) ≤ (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec ≤ b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : UInt64) : ((a + (b * c)) ≤ (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec ≤ b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]

example (a b c d e : USize) : ((a + (b * c)) ≤ (b - d / e)) ↔ (a.toBitVec + b.toBitVec * c.toBitVec ≤ b.toBitVec - d.toBitVec / e.toBitVec) := by
  simp only [int_toBitVec]
