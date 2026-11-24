import PEqualNP.CoRootGeometry3174
import PEqualNP.CoPhysical3174
import PEqualNP.CoNine3024Guided

namespace CoRule3174
open CoNine3024 CoThetaNine CoNine3024Path CoNine3024Transition CoNine3024Rows

theorem excludes (lower : SignedLower) (b : Fin 3) (inv : Bool) (ask : Canon.Oracle)
    (checked : Canon.run (Canon.guided (CoRoot3174.mode inv) ask) (geom (CoRoot3174.mode inv))
      13 (Canon.order (CoRoot3174.root b inv))=false) (k : Nat) (lim : k≤13) :
    ¬ CoClean3024.Clean ans k (CoPhysical3174.sources b inv) := by
  classical
  intro clean
  let p := CoRoot3174.mode inv
  let r := CoRoot3174.root b inv
  have img : (r.wires.map value).toFinset=CoPhysical3174.sources b inv := by
    rw [show r=CoRoot3174.root b inv from rfl,CoRootGeometry3174.images]
    rfl
  have sound : SoundGuard p (Canon.guided p ask) := by
    intro n cap S state small cone same nodup features
    exact Canon.guided_correct p ask state small cone (card_le cone) same nodup features
  obtain ⟨ic,dc,gc,ac⟩ := reorder p r img (CoRootGeometry3174.unique b inv)
    (CoRootGeometry3174.good b inv) (CoRootGeometry3174.initial b inv lim)
  have path := from_clean lower p _ sound clean lim (Canon.order r) ic dc gc ac
  exact Bool.false_ne_true (checked.symm.trans (Canon.complete path))

#print axioms excludes
end CoRule3174
