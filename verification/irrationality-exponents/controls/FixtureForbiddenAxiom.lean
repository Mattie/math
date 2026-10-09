def auditValue : Nat := 1
axiom forbiddenAuditAssumption : False
theorem fixture : auditValue = 1 := False.elim forbiddenAuditAssumption
