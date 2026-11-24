import Mathlib.Data.Finset.Card

namespace CoLeafRectangle3004
variable {P N V L : Type}
/-- With one leaf for each of two labels, a shared row and shared column
    forced into their respective leaves would place one cell in both. -/
theorem single_clash (label : L→V) (row : L→P→Prop) (col : L→N→Prop)
    (pick : P→N→L)
    (rectangle : ∀ l p n, row l p → col l n → pick p n=l)
    (rowIn : ∀ p n,row (pick p n) p) (colIn : ∀ p n,col (pick p n) n)
    (a b : V) (ne : a≠b) (p : P) (n : N)
    (forceArow : ∃ u,label (pick p u)=a) (forceBrow : ∃ u,label (pick p u)=b)
    (forceAcol : ∃ u,label (pick u n)=a) (forceBcol : ∃ u,label (pick u n)=b)
    (oneA : ∀ j k,label j=a → label k=a → j=k)
    (oneB : ∀ j k,label j=b → label k=b → j=k) : False := by
  obtain ⟨aN,ra⟩ := forceArow
  obtain ⟨bN,rb⟩ := forceBrow
  obtain ⟨aP,ca⟩ := forceAcol
  obtain ⟨bP,cb⟩ := forceBcol
  have ea := oneA _ _ ra ca
  have eb := oneB _ _ rb cb
  have x := rectangle _ p n (rowIn p aN) (ea.symm ▸ colIn aP n)
  have y := rectangle _ p n (rowIn p bN) (eb.symm ▸ colIn bP n)
  exact ne (ra.symm.trans ((congrArg label (x.symm.trans y)).trans rb))

end CoLeafRectangle3004
