import SlhDsaSecurity.Statement.Parameters

namespace SlhDsaSecurity

theorem parameters_consistent :
    totalHeight = layers * subtreeHeight ∧ messageDigits = 32 ∧ chains = 35 ∧
      forsTrees * forsHeight = 168 ∧ totalHeight - subtreeHeight = 54 ∧
      messageDigestBytes = 21 + 7 + 2 ∧ signatureBytes = 7856 := by
  decide +kernel

end SlhDsaSecurity
