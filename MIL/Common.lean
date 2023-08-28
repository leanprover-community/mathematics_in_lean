import Mathlib.Tactic

set_option warningAsError false

namespace PiNotation
open Lean.Parser Term
open Lean.PrettyPrinter.Delaborator

/-- Dependent function type (a "pi type"). The notation `Π x : α, β x` can
also be written as `(x : α) → β x`. -/
-- A direct copy of forall notation but with `Π`/`Pi` instead of `∀`/`Forall`.
@[term_parser]
def piNotation := leading_parser:leadPrec
  unicodeSymbol "Π" "Pi" >>
  many1 (ppSpace >> (binderIdent <|> bracketedBinder)) >>
  optType >> ", " >> termParser

/-- Dependent function type (a "pi type"). The notation `Π x ∈ s, β x` is
short for `Π x, x ∈ s → β x`. -/
-- A copy of forall notation from `Std.Util.ExtendedBinder` for pi notation
syntax "Π " binderIdent binderPred ", " term : term

macro_rules
  | `(Π $x:ident $pred:binderPred, $p) =>
    `(Π $x:ident, satisfies_binder_pred% $x $pred → $p)
  | `(Π _ $pred:binderPred, $p) =>
    `(Π x, satisfies_binder_pred% x $pred → $p)

/-- Since pi notation and forall notation are interchangable, we can
parse it by simply using the forall parser. -/
@[macro PiNotation.piNotation] def replacePiNotation : Lean.Macro
  | .node info _ args => return .node info ``Lean.Parser.Term.forall args
  | _ => Lean.Macro.throwUnsupported

/-- Override the Lean 4 pi notation delaborator with one that uses `Π`.
Note that this takes advantage of the fact that `(x : α) → p x` notation is
never used for propositions, so we can match on this result and rewrite it. -/
@[delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabForall
  -- Replacements
  let stx : Term ←
    match stx with
    | `($group:bracketedBinder → $body) => `(Π $group:bracketedBinder, $body)
    | _ => pure stx
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∀ ($i:ident : $_), $j:ident ∈ $s → $body) =>
      if i == j then `(∀ $i:ident ∈ $s, $body) else pure stx
    | `(∀ ($x:ident : $_), $y:ident > $z → $body) =>
      if x == y then `(∀ $x:ident > $z, $body) else pure stx
    | `(∀ ($x:ident : $_), $y:ident < $z → $body) =>
      if x == y then `(∀ $x:ident < $z, $body) else pure stx
    | `(∀ ($x:ident : $_), $y:ident ≥ $z → $body) =>
      if x == y then `(∀ $x:ident ≥ $z, $body) else pure stx
    | `(∀ ($x:ident : $_), $y:ident ≤ $z → $body) =>
      if x == y then `(∀ $x:ident ≤ $z, $body) else pure stx
    | `(Π ($i:ident : $_), $j:ident ∈ $s → $body) =>
      if i == j then `(Π $i:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  -- Merging
  match stx with
  | `(Π $group, Π $groups*, $body) => `(Π $group $groups*, $body)
  | _ => pure stx

-- the above delaborator and parser are still needed:
-- #check Π (x : Nat), Vector Bool x

end PiNotation

section SupInfNotation
open Lean Lean.PrettyPrinter.Delaborator

/-!
Improvements to the unexpanders in `Mathlib.Order.CompleteLattice`.

These are implemented as delaborators directly.
-/
@[delab app.iSup]
def iSup_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨆ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨆ ($x:ident : $dom), $body)
      else
        `(⨆ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨆ $x:ident, ⨆ (_ : $y:ident ∈ $s), $body)
    | `(⨆ ($x:ident : $_), ⨆ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨆ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

@[delab app.infᵢ]
def infᵢ_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, _, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨅ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨅ ($x:ident : $dom), $body)
      else
        `(⨅ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨅ $x:ident, ⨅ (_ : $y:ident ∈ $s), $body)
    | `(⨅ ($x:ident : $_), ⨅ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨅ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- The Exists notation has similar considerations as sup/inf -/
@[delab app.Exists]
def exists_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(∃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(∃ ($x:ident : $dom), $body)
      else
        `(∃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(∃ $i:ident, $j:ident ∈ $s ∧ $body)
    | `(∃ ($i:ident : $_), $j:ident ∈ $s ∧ $body) =>
      if i == j then `(∃ $i:ident ∈ $s, $body) else pure stx
    | `(∃ $x:ident, $y:ident > $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident > $z ∧ $body) =>
      if x == y then `(∃ $x:ident > $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident < $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident < $z ∧ $body) =>
      if x == y then `(∃ $x:ident < $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≥ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≥ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≥ $z, $body) else pure stx
    | `(∃ $x:ident, $y:ident ≤ $z ∧ $body)
    | `(∃ ($x:ident : $_), $y:ident ≤ $z ∧ $body) =>
      if x == y then `(∃ $x:ident ≤ $z, $body) else pure stx
    | _ => pure stx
  -- Merging
  match stx with
  | `(∃ $group:bracketedExplicitBinders, ∃ $groups*, $body) => `(∃ $group $groups*, $body)
  | _ => pure stx

-- the above delaborators are still needed:
-- #check ⨆ (i : Nat) (_ : i ∈ Set.univ), (i = i)
-- #check ∃ (i : Nat), i ≥ 3 ∧ i = i

end SupInfNotation

section UnionInterNotation
open Lean Lean.PrettyPrinter.Delaborator

/-!
Improvements to the unexpanders in `Mathlib.Data.Set.Lattice`.

These are implemented as delaborators directly.
-/

@[delab app.Set.unionᵢ]
def unionᵢ_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋃ ($x:ident : $dom), $body)
      else
        `(⋃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋃ $x:ident, ⋃ (_ : $y:ident ∈ $s), $body)
    | `(⋃ ($x:ident : $_), ⋃ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋃ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

@[delab app.Set.interᵢ]
def interᵢ_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName $ fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋂ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋂ ($x:ident : $dom), $body)
      else
        `(⋂ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋂ $x:ident, ⋂ (_ : $y:ident ∈ $s), $body)
    | `(⋂ ($x:ident : $_), ⋂ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋂ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

-- the above delaborators might not work correctly
-- #check ⋃ (s : Set ℕ) (_ : s ∈ Set.univ), s

end UnionInterNotation


namespace ProdProjNotation
open Lean Lean.PrettyPrinter.Delaborator

@[delab app.Prod.fst, delab app.Prod.snd]
def delabProdProjs : Delab := do
  let #[_, _, _] := (← SubExpr.getExpr).getAppArgs | failure
  let stx ← delabProjectionApp
  match stx with
  | `($(x).fst) => `($(x).1)
  | `($(x).snd) => `($(x).2)
  | _ => failure

/-! That works when the projection is a simple term, but we need
another approach when the projections are functions with applied arguments. -/

@[app_unexpander Prod.fst]
def unexpandProdFst : Lean.PrettyPrinter.Unexpander
  | `($(_) $p $xs*) => `($p.1 $xs*)
  | _ => throw ()

@[app_unexpander Prod.snd]
def unexpandProdSnd : Lean.PrettyPrinter.Unexpander
  | `($(_) $p $xs*) => `($p.2 $xs*)
  | _ => throw ()

example (p : Nat × Nat) : p.1 = p.2 → True := by simp
example (p : (Nat → Nat) × (Nat → Nat)) : p.1 22 = p.2 37 → True := by simp

end ProdProjNotation
