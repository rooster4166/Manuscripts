import GallaiLean.DenseRootB

/-! Audit A39b: which binders of the headline theorems are not used by their proof terms.
For each theorem, walk the lambda telescope of its value and report the binders whose free
variable does not occur in the body (types of later binders excluded). -/

open Lean Meta

def unusedBinders (n : Name) : MetaM (List Name) := do
  let some ci := (← getEnv).find? n | throwError "no {n}"
  let v ← match ci with
    | .thmInfo t => pure t.value
    | .defnInfo d => pure d.value
    | _ => throwError "no value for {n}"
  lambdaTelescope v fun xs body => do
    let mut out := []
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if !(body.containsFVar x.fvarId!) then
        -- also count use inside the types of later binders
        let later := xs.toList.dropWhile (· != x) |>.drop 1
        let mut usedLater := false
        for y in later do
          if (← y.fvarId!.getDecl).type.containsFVar x.fvarId! then usedLater := true
        if !usedLater then out := out ++ [decl.userName]
    return out

#eval do
  for n in [``Gallai.connector_core, ``Gallai.exists_lovasz_connector,
      ``Gallai.exists_decomp_of_connector, ``Gallai.exists_decomp_of_connector_mid,
      ``Gallai.test1At_of_connector, ``Gallai.test1At_of_connector_mid] do
    IO.println s!"{n}: unused binders {← unusedBinders n}"
