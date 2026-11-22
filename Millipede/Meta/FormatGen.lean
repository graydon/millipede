import Lean
import Millipede.Meta.Format

/-! ## The command `mp format` -/

namespace Millipede.Meta.Format

open Lean Elab Command Term Meta

/-! ### The proof of a generated function's obligations -/

/-- Forward chaining: replace each hypothesis `A → B` whose premise `fmt_pre` proves by `B`, in
passes over the hypotheses while one succeeds. -/
partial def fmtMp (passes : Nat := 8) : Tactic.TacticM Unit := do
  if passes == 0 then return
  let hyps : Tactic.TacticM (Array FVarId) := Tactic.withMainContext do
    return (← getLCtx).foldl (init := #[]) fun acc d =>
      if d.isImplementationDetail then acc else acc.push d.fvarId
  -- The callees' contracts are in the context latest call first, so the worklist starts from the
  -- end, and the hypotheses a success adds are tried next: a chain of calls resolves in one pass.
  let mut work := (← hyps).toList.reverse
  let mut progress := false
  let mut fuel := 4096
  while fuel > 0 do
    fuel := fuel - 1
    let fv :: rest := work | break
    work := rest
    let before ← hyps
    let g ← Tactic.getMainGoal
    let step ← g.withContext do
      let some d := (← getLCtx).find? fv | return false
      let ty ← instantiateMVars d.type
      let .forallE _ A B _ := ty | return false
      if B.hasLooseBVars then return false
      unless ← isProp A do return false
      let m ← mkFreshExprSyntheticOpaqueMVar A
      let s ← saveState
      let ok ← try
          let gs ← Tactic.run m.mvarId! (Tactic.evalTactic (← `(tactic| fmt_pre)))
          pure gs.isEmpty
        catch _ => pure false
      unless ok do
        s.restore
        return false
      let pf ← instantiateMVars m
      let g ← g.assert d.userName B (mkApp d.toExpr pf)
      let g ← (try g.clear d.fvarId catch _ => pure g)
      let (_, g) ← g.intro1P
      Tactic.replaceMainGoal [← splitAnds g]
      return true
    if step then
      progress := true
      let added := (← hyps).toList.filter (!before.contains ·)
      work := added ++ work
  if progress then fmtMp (passes - 1)

/-- `fmt_mp` replaces each hypothesis `A → B` whose premise `fmt_pre` proves by `B`. -/
elab "fmt_mp" : tactic => fmtMp

/-- `fmt_safe [defs]` proves the obligations of a generated parser, writer or validator. It splits
them as `mp_safe` does, with the lemmas the automatic attempt passes it, adds the callees'
contracts at their calls, and closes each piece by unfolding `defs`, forward chaining through the
contracts and `fmt_close`. -/
syntax (name := fmtSafe) "fmt_safe" " [" ident,* "]" : tactic

@[tactic fmtSafe] def evalFmtSafe : Tactic.Tactic := fun stx => do
  unfoldGoalDef
  Tactic.withMainContext do
  let env ← getEnv
  let goal ← instantiateMVars (← Tactic.getMainTarget)
  let some se := goal.find? (·.isAppOf ``Exp.safe)
    | throwError "fmt_safe: the goal is not the obligations of an `mp def`"
  let some tn := (se.getArg! 3).getAppFn.constName?
    | throwError "fmt_safe: the obligations of a term that is not an `mp def`'s"
  let some v := (env.find? tn).bind (·.value?) | throwError "fmt_safe: `{tn}` has no term"
  let callees := (fnsOf env v).filter (·.declName != tn.getPrefix)
  let simpLemma (n : Name) := `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  -- The splitting of `mp_safe`, with the lemmas the automatic attempt passes it, but without its
  -- closing `simp_all` and `grind` calls, which the walk below replaces. Its `simp` is not
  -- contextual, because the contextual one costs several times as much and the walk does not
  -- need it.
  let mut ls := #[← simpLemma tn, ← simpLemma ``Lens.fst, ← simpLemma ``Lens.snd]
  for g in callees do
    if g.hasSafe then ls := ls.push (← simpLemma (g.declName ++ `Safe'))
    if g.isRef then ls := ls.push (← simpLemma (g.declName ++ `req))
    if env.contains (g.declName ++ `post) then
      ls := ls.push (← simpLemma (g.declName ++ `exp_denote))
  let closers : Array Term := callees.filterMap fun g =>
    if g.hasSafe then some (mkCIdent (g.declName ++ `Safe')) else none
  let close ← closers.foldrM (fun c acc => `(tactic| first | (apply $c <;> assumption) | $acc:tactic))
    (← `(tactic| fail))
  Tactic.evalTactic (← `(tactic| set_option maxRecDepth 8192 in (
    intros
    mp_safe_setup
    set_option linter.unusedSimpArgs false in
    simp only [Millipede.Exp.safe, Millipede.Exp.denote,
      Millipede.Place.ok, Millipede.Place.get, Millipede.Place.set, Millipede.Atom.denote,
      Millipede.Env.get_here, Millipede.Env.get_there, Millipede.Env.set_here,
      Millipede.Env.set_there, Millipede.Args.denote, Millipede.RArgs.ok, Millipede.RArgs.denote,
      Millipede.RArgs.writeBack, Millipede.EArgs.ok, Millipede.EArgs.fill, Millipede.ExtSig.call,
      Millipede.EArgs.outCaps, Millipede.Guard.denote, Millipede.Place.check,
      Millipede.Prim.denote, Millipede.Prim.ok, Millipede.vrange, Millipede.Ctor.pairMk_build,
      Millipede.vview_isFull, Millipede.Slots.isFull_setCell, Millipede.sview_isFull,
      Millipede.sunview_isFull, Millipede.Carry.get, Millipede.Carry.set,
      Millipede.Flat.tupBuild_cons, Millipede.Flat.tupBuild_nil, Millipede.Ctor.tupMk,
      true_and, and_true, $ls,*] at *
    repeat' (first
      | exact trivial
      | $close:tactic
      | mp_loop_split
      | apply And.intro
      | intro _))))
  let withPost := (callees.filter fun g => env.contains (g.declName ++ `post)).map
    fun g => mkCIdent g.declName
  Tactic.evalTactic (← `(tactic| all_goals (try mp_inst_posts keep [$withPost,*])))
  let defs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← stx[2].getSepArgs.mapM fun d =>
    `(Lean.Parser.Tactic.simpLemma| $(⟨d⟩):ident)
  -- Each goal by the walk; what it leaves, as the automatic attempt would close it.
  Tactic.evalTactic (← `(tactic| all_goals (first
    | (fmt_norm
       (try simp only [$defs,*, decide_eq_true_eq, ← UInt64.toNat_inj, UInt64.reduceToNat] at *)
       fmt_split
       fmt_mp
       fmt_close)
    | (set_option linter.unusedSimpArgs false in
        simp_all [UInt64.toNat_ofNat', Nat.mod_eq_of_lt, $defs,*]; done))))

/-- What the generator records of a structure with a format: the name of its description and the
description's `maxSize`. -/
structure FmtInfo where
  struct : Name
  fmtName : Name
  maxSize : Nat
deriving Inhabited

/-- The structures with a format, so that a later format can contain them. -/
initialize formatExt : SimplePersistentEnvExtension FmtInfo (NameMap FmtInfo) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m i => m.insert i.struct i
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m i => m.insert i.struct i) m) {}
  }

register_option mp.format.seedBug : Nat := {
  defValue := 0
  descr := "test only: `mp format` emits a wrong parser, to show that its contract proof then \
    fails: 1 reads the first integer in the other byte order, 2 gives each arm of the first union \
    the code of the next arm"
}

/-- A leaf of a description. -/
inductive Leaf where
  | uint (k : Nat) (big : Bool)
  | lbytes (k : Nat) (big : Bool) (max : Nat)
  | unit
  | bytes (n : Nat)
  | skip (n : Nat)
  /-- The constant whose `k` big-endian bytes are those of `v`. -/
  | const (k v : Nat)
deriving Inhabited, BEq

/-- A node of a description, with the field of the structure it fills. -/
inductive Node where
  /-- A leaf in the field `fld`, with the text of its description. -/
  | leaf (fld : Option Name) (l : Leaf) (fmt : String)
  /-- A structure with a format, in the field `fld`. -/
  | sub (fld : Name) (S : Name) (info : FmtInfo)
  /-- A union whose tag is the field `fld`, with its arms. -/
  | union (fld : Name) (k : Nat) (big : Bool) (arms : List (Nat × List Node))
  /-- A repetition of the structure `S`, which has a format, in the field `fld : Seq S M`. -/
  | array (fld : Name) (k : Nat) (big : Bool) (max : Nat) (S : Name) (info : FmtInfo)
deriving Inhabited

/-! ### Syntax -/

/-- The description of a field. -/
declare_syntax_cat mpFmt (behavior := both)
/-- A field and its description; `_` for bytes that fill no field. -/
syntax mpFmtField := (ident <|> "_") " : " mpFmt
/-- A record: its fields in order. `()` is the empty record. -/
syntax mpFmtRec := "(" mpFmtField,* ")"
/-- An arm of a union. -/
syntax mpFmtArm := " | " num " => " mpFmtRec
/-- An unsigned integer of `k` bytes, `big` or `little` endian. -/
syntax (name := fmtUint) &"uint " num ident : mpFmt
/-- A byte string with a length of `k` bytes, of at most `max` bytes. -/
syntax (name := fmtLBytes) &"lbytes " num ident num : mpFmt
/-- A tag of `k` bytes, then the record of the arm with that tag. -/
syntax (name := fmtUnion) &"union " num ident mpFmtArm+ : mpFmt
/-- A count of `k` bytes, at most `max`, then that many values of the structure `S`. -/
syntax (name := fmtArray) &"array " num ident num ident : mpFmt
/-- `n` bytes, held in an `Arr UInt8 n`. -/
syntax (name := fmtBytes) &"bytes " num : mpFmt
/-- `n ≤ 8` ignored bytes, written as zeros; they fill no field. -/
syntax (name := fmtSkip) &"skip " num : mpFmt
/-- The bytes given, at most 8, which must be present; they fill no field. -/
syntax (name := fmtConst) &"const " "[" num,* "]" : mpFmt
/-- A named description (a leaf `Fmt`), or a structure that has a format. -/
syntax (name := fmtName) ident : mpFmt

/-- `mp format f for T := (x : uint 2 big, …)` defines the description `f`, the abstraction
`T.toVal`, the bounds `T.Bound`, and the parser `T.parseAt` and writer `T.writeAt` with their
contracts proved. -/
syntax (name := mpFormat) (docComment)? mpKw &"format " ident &" for " ident " := " mpFmtRec :
  command

/-! ### From syntax to nodes -/

/-- The byte order named by `big` or `little`. -/
def endianOf (id : Syntax) : CommandElabM Bool :=
  match id.getId with
  | `big => pure true
  | `little => pure false
  | _ => throwErrorAt id "mp format: the byte order is `big` or `little`, not `{id.getId}`"

/-- The leaf a named description stands for. -/
def leafOfConst (id : Syntax) (c : Name) : CommandElabM Leaf := do
  let some ci := (← getEnv).find? c | throwErrorAt id "mp format: unknown `{c}`"
  unless ci.type.isConstOf ``Millipede.Format.Fmt do
    throwErrorAt id "mp format: `{c}` is neither a description (`Fmt`) nor a structure with a \
      format"
  let l? ← liftTermElabM do
    let e ← whnf (mkConst c)
    let args := e.getAppArgs
    let nat (i : Nat) : MetaM (Option Nat) := evalNat (args[i]!)
    let big (i : Nat) : MetaM (Option Bool) := do
      match (← whnf args[i]!).constName? with
      | some ``Millipede.Format.Endian.big => pure (some true)
      | some ``Millipede.Format.Endian.little => pure (some false)
      | _ => pure none
    match e.getAppFn.constName? with
    | some ``Millipede.Format.Fmt.uint => do
      let some k ← nat 0 | return none
      let some b ← big 1 | return none
      return some (Leaf.uint k b)
    | some ``Millipede.Format.Fmt.lbytes => do
      let some k ← nat 0 | return none
      let some b ← big 1 | return none
      let some m ← nat 2 | return none
      return some (Leaf.lbytes k b m)
    | some ``Millipede.Format.Fmt.unit => return some .unit
    | _ => return none
  let some l := l? | throwErrorAt id "mp format: `{c}` must be a leaf (`uint`, `lbytes` or \
    `unit`) with literal parameters to describe one field"
  return l

/-- The text of a leaf's description. -/
def leafText : Leaf → String
  | .uint k b => s!"(.uint {k} {if b then ".big" else ".little"})"
  | .lbytes k b m => s!"(.lbytes {k} {if b then ".big" else ".little"} {m})"
  | .unit => ".unit"
  | .bytes n => s!"(.bytes {n})"
  | .skip n => s!"(.skip {n})"
  | .const k v => s!"(.const (Millipede.Format.encUint {k} .big {v}))"

mutual
/-- The node of a field. -/
partial def nodeOf (fld : Syntax) : CommandElabM Node := do
  let nm? : Option Name := if fld[0].isIdent then some fld[0].getId else none
  let d := fld[2]
  let need (what : String) : CommandElabM Name := do
    let some n := nm? | throwErrorAt fld[0] "mp format: {what} fills a field; name it"
    pure n
  let k := d[1].isNatLit?.getD 0
  match d.getKind with
  | ``fmtUint =>
    let l := Leaf.uint k (← endianOf d[2])
    return .leaf (some (← need "an integer")) l (leafText l)
  | ``fmtLBytes =>
    let l := Leaf.lbytes k (← endianOf d[2]) (d[3].isNatLit?.getD 0)
    return .leaf (some (← need "a byte string")) l (leafText l)
  | ``fmtUnion =>
    let arms ← d[3].getArgs.toList.mapM fun a => do
      return (a[1].isNatLit?.getD 0, ← recOf a[3])
    return .union (← need "the tag of a union") k (← endianOf d[2]) arms
  | ``fmtBytes =>
    let l := Leaf.bytes k
    return .leaf (some (← need "`bytes`")) l (leafText l)
  | ``fmtSkip =>
    if let some x := nm? then
      throwErrorAt fld[0] "mp format: `skip` fills no field; write `_ : skip {k}`, not `{x}`"
    unless k ≤ 8 do throwErrorAt d "mp format: `skip {k}`: at most 8 ignored bytes"
    let l := Leaf.skip k
    return .leaf none l (leafText l)
  | ``fmtConst =>
    if let some x := nm? then
      throwErrorAt fld[0] "mp format: `const` fills no field; write `_ : const […]`, not `{x}`"
    let bs := d[2].getSepArgs.toList.map (·.isNatLit?.getD 0)
    unless 1 ≤ bs.length ∧ bs.length ≤ 8 do
      throwErrorAt d "mp format: a `const` has 1 to 8 bytes"
    if bs.any (· ≥ 256) then throwErrorAt d "mp format: a `const` byte is below 256"
    let l := Leaf.const bs.length (bs.foldl (fun a b => a * 256 + b) 0)
    return .leaf none l (leafText l)
  | ``fmtArray =>
    let id := d[4]
    let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let some i := (formatExt.getState (← getEnv)).find? c
      | throwErrorAt id "mp format: the elements of an `array` are a structure with a format; \
          `{c}` has none"
    return .array (← need "an array") k (← endianOf d[2]) (d[3].isNatLit?.getD 0) c i
  | ``fmtName =>
    let id := d[0]
    let env ← getEnv
    match ← liftCoreM (observing (realizeGlobalConstNoOverloadWithInfo id)) with
    | .ok c =>
      if let some i := (formatExt.getState env).find? c then
        return .sub (← need s!"the structure `{c}`") c i
      if isStructure env c then
        throwErrorAt id "mp format: the structure `{c}` has no format; give it one with \
          `mp format … for {c}` first"
      let l ← leafOfConst id c
      let f ← if l == .unit then pure nm? else some <$> need s!"`{c}`"
      return .leaf f l s!"{c}"
    | .error _ => throwErrorAt id "mp format: unknown description or structure `{id.getId}`"
  | _ => throwErrorAt d "mp format: unknown description"

/-- The nodes of a record. -/
partial def recOf (r : Syntax) : CommandElabM (List Node) :=
  r[1].getSepArgs.toList.mapM nodeOf
end

/-! ### Checks against the structure -/

/-- The fields of `T` with their types. -/
def fieldsOf (T : Name) : CommandElabM (List (Name × Expr)) := do
  let env ← getEnv
  let some info := getStructureInfo? env T
    | throwError "mp format: `{T}` is not a structure"
  liftTermElabM do
    info.fieldNames.toList.mapM fun f => do
      let some proj := getProjFnForField? env T f | throwError "mp format: no projection {f}"
      let ty ← inferType (mkConst proj)
      return (f, ty.bindingBody!)

/-- Check one use of a field against its type. -/
def checkField (ref : Syntax) (T : Name) (fs : List (Name × Expr)) (x : Name) (what : String)
    (ok : Expr → MetaM (Option String)) : CommandElabM Unit := do
  let some (_, ty) := fs.find? (·.1 == x)
    | throwErrorAt ref "mp format: `{T}` has no field `{x}` (the description reads {what} into it)"
  if let some msg ← liftTermElabM (ok ty) then
    let tyS := toString (← liftTermElabM (ppExpr ty))
    throwErrorAt ref "mp format: the field `{x}` of `{T}` has type `{tyS}`, \
      but {msg}"

/-- The checks of a description against the structure, with the fields filled so far on the
path. -/
partial def checkNodes (ref : Syntax) (T : Name) (fs : List (Name × Expr)) :
    List Node → StateT (List Name) CommandElabM Unit
  | [] => pure ()
  | n :: rest => do
    let use (x : Name) : StateT (List Name) CommandElabM Unit := do
      if (← get).contains x then
        throwErrorAt ref "mp format: the field `{x}` is filled twice on one path through the \
          description"
      modify (x :: ·)
    match n with
    | .leaf none _ _ => pure ()
    | .leaf (some x) (.uint k _) _ =>
      unless 1 ≤ k ∧ k ≤ 8 do
        throwErrorAt ref "mp format: `uint {k}` for `{x}`: an integer has 1 to 8 bytes"
      checkField ref T fs x s!"`uint {k}`" fun ty => pure <|
        if ty.isConstOf ``UInt64 then none else some s!"`uint {k}` needs `UInt64`"
      use x
    | .leaf (some x) (.lbytes k _ m) _ =>
      unless 1 ≤ k ∧ k ≤ 8 do
        throwErrorAt ref "mp format: `lbytes {k}` for `{x}`: a length has 1 to 8 bytes"
      checkField ref T fs x s!"`lbytes {k} _ {m}`" fun ty => do
        if ty.isAppOfArity ``Millipede.Format.LBytes 1 then
          let some cap ← evalNat ty.appArg! | return some "its bound is not a literal"
          if m ≤ cap then return none
          return some s!"a byte string of at most {m} bytes does not fit in `LBytes {cap}`"
        return some s!"`lbytes` needs `LBytes M` with `{m} ≤ M`"
      use x
    | .leaf (some x) .unit _ => throwErrorAt ref "mp format: `{x}`: an empty record fills no field"
    | .leaf (some x) (.bytes n) _ =>
      checkField ref T fs x s!"`bytes {n}`" fun ty => do
        let ty ← whnfR ty
        if ty.isAppOfArity ``Vector 2 && ty.appFn!.appArg!.isConstOf ``UInt8 then
          let some cap ← evalNat ty.appArg! | return some "its length is not a literal"
          if n == cap then return none
          return some s!"`bytes {n}` needs `Arr UInt8 {n}`"
        return some s!"`bytes {n}` needs `Arr UInt8 {n}`"
      use x
    | .leaf (some _) _ _ => pure ()
    | .sub x S _ =>
      checkField ref T fs x s!"`{S}`" fun ty => pure <|
        if ty.isConstOf S then none else some s!"the description reads a `{S}`"
      use x
    | .array x k _ m S _ =>
      unless 1 ≤ k ∧ k ≤ 8 do
        throwErrorAt ref "mp format: `array {k}` for `{x}`: a count has 1 to 8 bytes"
      checkField ref T fs x s!"`array {k} _ {m} {S}`" fun ty => do
        if ty.isAppOfArity ``Millipede.Format.Seq 2 && ty.appFn!.appArg!.isConstOf S then
          let some cap ← evalNat ty.appArg! | return some "its bound is not a literal"
          if m ≤ cap then return none
          return some s!"an array of at most {m} elements does not fit in `Seq {S} {cap}`"
        return some s!"`array … {S}` needs `Seq {S} M` with `{m} ≤ M`"
      let inh ← liftTermElabM do
        try discard <| synthInstance (mkApp (mkConst ``Inhabited [1]) (mkConst S)); pure true
        catch _ => pure false
      unless inh do
        throwErrorAt ref "mp format: the elements of `{x}` need `Inhabited {S}` (add `deriving \
          Inhabited` to `{S}`)"
      use x
    | .union x k _ arms =>
      unless 1 ≤ k ∧ k ≤ 8 do
        throwErrorAt ref "mp format: `union {k}` for `{x}`: a tag has 1 to 8 bytes"
      checkField ref T fs x s!"the tag of a `union {k}`" fun ty => pure <|
        if ty.isConstOf ``UInt64 then none else some "the tag of a union needs `UInt64`"
      use x
      let tags := arms.map (·.1)
      for t in tags do
        unless t < 256 ^ k do
          throwErrorAt ref "mp format: the arm tag {t} of `{x}` does not fit in {k} byte(s)"
      if let some t := tags.find? (fun t => tags.count t > 1) then
        throwErrorAt ref "mp format: the arm tag {t} of `{x}` appears twice; the second arm \
          would never be used"
      let st ← get
      for (_, ns) in arms do
        set st
        checkNodes ref T fs (ns ++ rest)
      return
    checkNodes ref T fs rest

/-- The fields a description fills on some path. -/
partial def usedFields : List Node → List Name
  | [] => []
  | .leaf (some x) _ _ :: r => x :: usedFields r
  | .leaf none _ _ :: r => usedFields r
  | .sub x _ _ :: r => x :: usedFields r
  | .array x _ _ _ _ _ :: r => x :: usedFields r
  | .union x _ _ arms :: r => x :: (arms.flatMap (usedFields ·.2) ++ usedFields r)

/-- The structures with a format that a description contains. -/
partial def subsOf : List Node → List FmtInfo
  | [] => []
  | .sub _ _ i :: r => i :: subsOf r
  | .array _ _ _ _ _ i :: r => i :: subsOf r
  | .union _ _ _ arms :: r => arms.flatMap (subsOf ·.2) ++ subsOf r
  | _ :: r => subsOf r

/-- The named leaf descriptions of a record, to unfold. -/
partial def leafNames : List Node → List String
  | [] => []
  | .leaf _ _ t :: r => (if t.startsWith "(" || t.startsWith "." then [] else [t]) ++ leafNames r
  | .union _ _ _ arms :: r => arms.flatMap (leafNames ·.2) ++ leafNames r
  | _ :: r => leafNames r

/-! ### Generated text -/

/-- The largest number of bytes, as `Fmt.maxSize` computes it. -/
partial def maxSizeOf : List Node → Nat
  | [] => 0
  | n :: r => (match n with
    | .leaf _ (.uint k _) _ => k
    | .leaf _ (.lbytes k _ m) _ => k + m
    | .leaf _ .unit _ => 0
    | .leaf _ (.bytes n) _ => n
    | .leaf _ (.skip n) _ => n
    | .leaf _ (.const k _) _ => k
    | .sub _ _ i => i.maxSize
    | .array _ k _ m _ i => k + m * i.maxSize
    | .union _ k _ arms => k + arms.foldr (fun a m => max (maxSizeOf a.2) m) 0) + maxSizeOf r

mutual
/-- The description of a record: nested pairs. -/
partial def fmtText : List Node → String
  | [] => ".unit"
  | [n] => nodeFmt n
  | n :: r => s!"(.pair {nodeFmt n} {fmtText r})"
/-- The description of a node. -/
partial def nodeFmt : Node → String
  | .leaf _ _ t => t
  | .sub _ _ i => s!"{i.fmtName}"
  | .array _ k b m _ i => s!"(.array {k} {if b then ".big" else ".little"} {m} {i.fmtName})"
  | .union _ k b arms =>
    let a := arms.foldr (fun (t, ns) acc => s!"(.arm {t} {fmtText ns} {acc})") ".noArm"
    s!"(.union {k} {if b then ".big" else ".little"} {a})"
end

mutual
/-- The abstraction of a record of `r`. -/
partial def valText : List Node → String
  | [] => ".unit"
  | [n] => nodeVal n
  | n :: r => s!"(.pair {nodeVal n} {valText r})"
/-- The abstraction of a node of `r`. -/
partial def nodeVal : Node → String
  | .leaf (some x) (.uint _ _) _ => s!"(.num r.{x}.toNat)"
  | .leaf (some x) (.lbytes _ _ _) _ => s!"(Millipede.Format.LBytes.toVal r.{x})"
  | .leaf (some x) (.bytes n) _ => s!"(.bytes (r.{x}.toList.take {n}))"
  | .leaf _ _ _ => ".unit"
  | .sub x S _ => s!"({S}.toVal r.{x})"
  | .array x _ _ _ S _ => s!"(Millipede.Format.Seq.toValWith {S}.toVal r.{x})"
  | .union x _ _ arms =>
    let a := arms.foldr (fun (t, ns) acc => s!"if r.{x}.toNat = {t} then {valText ns} else {acc}")
      ".unit"
    s!"(.tag r.{x}.toNat ({a}))"
end

/-- The bounds a record of `r` keeps, as conjuncts. -/
partial def boundsOf : List Node → List String
  | [] => []
  | n :: r => (match n with
    | .leaf (some x) (.lbytes _ _ m) _ => [s!"r.{x}.len.toNat ≤ {m}"]
    | .sub x S _ => [s!"{S}.Bound r.{x}"]
    | .array x _ _ m S _ => [s!"Millipede.Format.Seq.Bound {S}.Bound {m} r.{x}"]
    | .union x _ _ arms => arms.filterMap fun (t, ns) =>
      match boundsOf ns with
      | [] => none
      | bs => some s!"(r.{x} = {t} → {" ∧ ".intercalate bs})"
    | _ => []) ++ boundsOf r

/-- The statements of the parser of a record, then of `rest`. The state counts the unions, to
name their tags, and records whether an integer was read, for the seeded bug 1. -/
partial def parseStmts (seed : Nat) (ind : String) : List Node → StateM (Nat × Bool) (List String)
  | [] => pure [ind ++ "return true"]
  | n :: rest => do
    let call (c : String) : List String :=
      [s!"{ind}let ok := {c}", s!"{ind}if !ok then return false"]
    match n with
    | .leaf (some x) (.uint k b) _ =>
      let (c, used) ← get
      let b := if seed == 1 && !used then !b else b
      set (c, true)
      return call s!"parseUint (&s) (&mut pos) {k} {b} (&mut out.{x})" ++
        (← parseStmts seed ind rest)
    | .leaf (some x) (.lbytes k b m) _ =>
      return call s!"parseLBytes (&s) (&mut pos) {k} {b} {m} (&mut out.{x})" ++
        (← parseStmts seed ind rest)
    | .leaf (some x) (.bytes n) _ =>
      return call s!"parseBytes (&s) (&mut pos) {n} (&mut out.{x})" ++ (← parseStmts seed ind rest)
    | .leaf _ (.skip n) _ =>
      return call s!"skipBytes (&s) (&mut pos) {n}" ++ (← parseStmts seed ind rest)
    | .leaf _ (.const k v) _ =>
      return call s!"parseConst (&s) (&mut pos) {k} {v}" ++ (← parseStmts seed ind rest)
    | .leaf _ _ _ => parseStmts seed ind rest
    | .sub x S _ =>
      return call s!"{S}.parseAt (&s) (&mut pos) (&mut out.{x})" ++ (← parseStmts seed ind rest)
    | .array x k b m S _ =>
      let (c, used) ← get
      set (c + 1, used)
      let n := s!"count{c}"
      return call s!"parseUint (&s) (&mut pos) {k} {b} (&mut out.{x}.len)" ++
        [s!"{ind}let {n} := out.{x}.len", s!"{ind}if {n} > {m} then return false"] ++
        call s!"{S}.parseItems (&s) (&mut pos) {n} (&mut out.{x}.data)" ++
        (← parseStmts seed ind rest)
    | .union x k b arms =>
      let (c, used) ← get
      set (c + 1, used)
      let t := s!"tag{c}"
      let bodies ← arms.mapM fun (_, ns) => parseStmts seed (ind ++ "  ") (ns ++ rest)
      -- The seeded bug 2 gives each arm of the first union the code of the next arm.
      let bodies := if seed == 2 && c == 0 && bodies.length > 1 then
        bodies.drop 1 ++ bodies.take 1 else bodies
      let arms := (arms.zip bodies).flatMap fun ((tg, _), body) =>
        s!"{ind}if {t} == {tg} then" :: body
      return call s!"parseUint (&s) (&mut pos) {k} {b} (&mut out.{x})" ++
        [s!"{ind}let {t} := out.{x}"] ++ arms ++ [s!"{ind}return false"]

/-- The statements of the validator of a record, then of `rest`. The state counts the unions. -/
partial def validStmts (ind : String) : List Node → StateM Nat (List String)
  | [] => pure [ind ++ "return true"]
  | n :: rest => do
    let call (c : String) : List String :=
      [s!"{ind}let ok := {c}", s!"{ind}if !ok then return false"]
    match n with
    | .leaf _ (.uint k b) _ =>
      return call s!"checkUint (&s) (&mut pos) {k} {b}" ++ (← validStmts ind rest)
    | .leaf _ (.lbytes k b m) _ =>
      return call s!"checkLBytes (&s) (&mut pos) {k} {b} {m}" ++ (← validStmts ind rest)
    | .leaf _ .unit _ => validStmts ind rest
    | .leaf _ (.bytes n) _ =>
      return call s!"checkBytes (&s) (&mut pos) {n}" ++ (← validStmts ind rest)
    | .leaf _ (.skip n) _ =>
      return call s!"skipBytes (&s) (&mut pos) {n}" ++ (← validStmts ind rest)
    | .leaf _ (.const k v) _ =>
      return call s!"parseConst (&s) (&mut pos) {k} {v}" ++ (← validStmts ind rest)
    | .sub _ S _ => return call s!"{S}.validAt (&s) (&mut pos)" ++ (← validStmts ind rest)
    | .array _ k b m S _ =>
      let c ← get
      set (c + 1)
      let n := s!"count{c}"
      return [s!"{ind}let mut {n} : UInt64 := 0"] ++
        call s!"parseUint (&s) (&mut pos) {k} {b} (&mut {n})" ++
        [s!"{ind}if {n} > {m} then return false"] ++
        call s!"{S}.validItems_{m} (&s) (&mut pos) {n}" ++ (← validStmts ind rest)
    | .union _ k b arms =>
      let c ← get
      set (c + 1)
      let t := s!"tag{c}"
      let bodies ← arms.mapM fun (_, ns) => validStmts (ind ++ "  ") (ns ++ rest)
      let arms := (arms.zip bodies).flatMap fun ((tg, _), body) =>
        s!"{ind}if {t} == {tg} then" :: body
      return [s!"{ind}let mut {t} : UInt64 := 0"] ++
        call s!"parseUint (&s) (&mut pos) {k} {b} (&mut {t})" ++ arms ++ [s!"{ind}return false"]

/-- The statements of the writer of a record, then of `rest`. The state counts the unions. -/
partial def writeStmts (ind : String) : List Node → StateM Nat (List String)
  | [] => pure []
  | n :: rest => do
    match n with
    | .leaf (some x) (.uint k b) _ =>
      return s!"{ind}writeUint (&mut d) (&mut pos) {k} {b} v.{x}" :: (← writeStmts ind rest)
    | .leaf (some x) (.lbytes k b _) _ =>
      return s!"{ind}writeLBytes (&mut d) (&mut pos) {k} {b} (&v.{x})" :: (← writeStmts ind rest)
    | .leaf (some x) (.bytes n) _ =>
      return s!"{ind}writeBytes (&mut d) (&mut pos) {n} (&v.{x})" :: (← writeStmts ind rest)
    | .leaf _ (.skip n) _ =>
      return s!"{ind}writeSkip (&mut d) (&mut pos) {n}" :: (← writeStmts ind rest)
    | .leaf _ (.const k v) _ =>
      return s!"{ind}writeConst (&mut d) (&mut pos) {k} {v}" :: (← writeStmts ind rest)
    | .leaf _ _ _ => writeStmts ind rest
    | .sub x S _ =>
      return s!"{ind}{S}.writeAt (&mut d) (&mut pos) (&v.{x})" :: (← writeStmts ind rest)
    | .array x k b _ S _ =>
      return [s!"{ind}writeUint (&mut d) (&mut pos) {k} {b} v.{x}.len",
        s!"{ind}{S}.writeItems (&mut d) (&mut pos) v.{x}.len (&v.{x}.data)"] ++
        (← writeStmts ind rest)
    | .union x k b arms =>
      let c ← get
      set (c + 1)
      let t := s!"tag{c}"
      let ind' := ind ++ "  "
      let bodies ← arms.filterMapM fun (tg, ns) => do
        let body ← writeStmts ind' (ns ++ rest)
        return if body.isEmpty then none else some (tg, body)
      let other ← writeStmts ind' rest
      let chain := match bodies with
        | [] => other.map fun l => (l.drop 2).toString
        | (tg, body) :: more =>
          (s!"{ind}if {t} == {tg} then" :: body) ++
          more.flatMap (fun (tg, body) => s!"{ind}else if {t} == {tg} then" :: body) ++
          (if other.isEmpty then [] else s!"{ind}else" :: other)
      return [s!"{ind}writeUint (&mut d) (&mut pos) {k} {b} v.{x}", s!"{ind}let {t} := v.{x}"] ++
        chain

/-! ### Elaborating the generated commands -/

/-- Give every node of `stx` the source information `si`, so that messages point at the
command. -/
partial def setInfo (si : SourceInfo) : Syntax → Syntax
  | .node _ k as => .node si k (as.map (setInfo si))
  | .atom _ v => .atom si v
  | .ident _ r v p => .ident si r v p
  | .missing => .missing

/-- Parse and elaborate one generated command. A command that logs an error stops `mp format`,
with `what` saying which generated declaration failed. -/
def runGen (ref : Syntax) (what : String) (src : String) : CommandElabM Unit := do
  let stx ← match Parser.runParserCategory (← getEnv) `command src "<mp format>" with
    | .ok s => pure s
    | .error e => throwErrorAt ref "mp format: internal error, the generated text does not \
        parse: {e}\n{src}"
  let log := (← get).messages
  withRef ref <| elabCommand (setInfo (SourceInfo.fromRef ref) stx)
  let errs := (← get).messages.toList.drop log.toList.length |>.filter (·.severity == .error)
  if let some e := errs.head? then
    -- The generated command's own messages are replaced by one that names it, with the first
    -- line of its first error.
    let first := ((← e.data.toString).splitOn "\n").headD ""
    modify fun st => { st with messages := log }
    throwErrorAt ref "mp format: {what} failed, so the description is not accepted ({first})"

/-- The `open`s and options of every generated command. -/
def preamble : String :=
  "set_option experimental.vcgen true in\nopen Millipede Millipede.Format Std.WP in\n"


/-- The repetitions in a description: the element structure, its format and the bound. -/
partial def arraysOf : List Node → List (Name × FmtInfo × Nat)
  | [] => []
  | .array _ _ _ m S i :: r => (S, i, m) :: arraysOf r
  | .union _ _ _ arms :: r => arms.flatMap (arraysOf ·.2) ++ arraysOf r
  | _ :: r => arraysOf r

/-- The element loops of a structure `S` with the format `F` of at most `sz` bytes: a parser and a
writer over `Arr S M` for every `M`, proved once with the invariants `ItemsInv` and `WItemsInv`. -/
def itemsText (S Sd F : Name) (sz : Nat) : List (String × String) :=
  [("the section of the generated code", "section"),
   ("the section of the generated code",
    "variable (fmtN fmtM : Nat) (fmtHN : fmtN < 2 ^ 64) (fmtHM : fmtM < 2 ^ 64)"),
   ("the section of the generated code", "include fmtHN fmtHM"),
   (s!"the element parser `{S}.parseItems`", preamble ++
    s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
    /-- Parse `n` values of `{S}` one after another into the first `n` elements of `out`. -/\n\
    mp def {Sd}.parseItems (s : &[UInt8; fmtN]) (pos : &mut UInt64) (n : UInt64) (out : &mut Arr {S} fmtM)\n    \
      requires pos.toNat ≤ s.len.toNat ∧ n.toNat ≤ fmtM\n    \
      ensures ItemsP {F} (Slots.bytes s s.len.toNat) pos n.toNat result pos'\n        \
        ((out'.toList.take n.toNat).map {S}.toVal) ∧\n      \
        (result = true → pos'.toNat ≤ s.len.toNat ∧\n        \
          ∀ i (h : i < fmtM), i < n.toNat → {S}.Bound out'[i]) : Bool := do\n  \
    let mut good := true\n  \
    for i in 0...fmtM do\n    \
      if i ≥ n then break\n    \
      if good then\n      \
        good := {S}.parseAt (&s) (&mut pos) (&mut out[i]!)\n  \
    good"),
   (s!"the proof of the element parser's contract `{S}.parseItems.spec`", preamble ++
    s!"mp prove {Sd}.parseItems.spec := by\n  \
  intro s sl pos n out\n  \
  vcgen [{S}.parseItems] invariants\n  \
  · fun done _ (good, p, o, _) => ItemsInv {F} {S}.toVal {S}.Bound (Slots.bytes s sl.toNat) pos\n      \
      (min done.length n.toNat) good p o\n  \
  all_goals try dsimp only at *\n  \
  case vc1 hpre => exact ItemsInv.init (by simpa using hpre.1.1)\n  \
  case vc2 hpre good p o _ hinv =>\n    \
    rw [List.length_range, Nat.min_eq_right hpre.1.2] at hinv\n    \
    simpa using hinv.done\n  \
  case vc3 hpre pref cur suff hr good p o _ hinv hc hg =>\n    \
    subst hg; exact ⟨by simpa using hinv.pos_le, hpre.2⟩\n  \
  case vc4 hpre pref cur suff hr good p o _ hinv hc hg ok x p' _ hx =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    subst hg\n    \
    rw [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)]\n    \
    simp only [List.length_append, List.length_singleton,\n      \
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)]\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    exact hinv.call (by simpa using hpre.1.1) (by omega) hx.1 (by simpa using hx.2)\n  \
  case vc5 hpre pref cur suff hr good p o _ hinv hc hg =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    simp only [Bool.not_eq_true] at hg; subst hg\n    \
    simp only [List.length_append, List.length_singleton,\n      \
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)]\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    exact hinv.skip\n  \
  case vc6 hpre pref cur suff hr good p o _ hinv hc =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    rw [List.length_range, Nat.min_eq_right (by omega)]\n    \
    rw [Nat.min_eq_right (by omega)] at hinv\n    \
    exact hinv"),
   (s!"the proof of the element parser's obligations `{S}.parseItems.safe`", preamble ++
    s!"mp prove {Sd}.parseItems.safe := by\n  \
  mp_auto invariants\n  \
  · fun _ _ (good, p, _, _) => good = true → p.toNat ≤ s.len.toNat"),
   (s!"the element writer `{S}.writeItems`", preamble ++
    s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
    /-- Write the first `n` elements of `a`, values of `{S}`, one after another. -/\n\
    mp def {Sd}.writeItems (d : &mut [UInt8; fmtN]) (pos : &mut UInt64) (n : UInt64) (a : &Arr {S} fmtM)\n    \
      requires pos.toNat + n.toNat * {sz} ≤ d.len.toNat ∧ n.toNat ≤ fmtM ∧\n      \
        ∀ i (h : i < fmtM), i < n.toNat → {S}.Bound a[i]\n    \
      ensures WrittenItems {F} d d' pos pos' ((a.toList.take n.toNat).map {S}.toVal) ∧\n      \
        pos'.toNat ≤ pos.toNat + n.toNat * {sz} : Unit := do\n  \
    for i in 0...fmtM do\n    \
      if i ≥ n then break\n    \
      {S}.writeAt (&mut d) (&mut pos) (&a[i]!)"),
   (s!"the proof of the element writer's contract `{S}.writeItems.spec`", preamble ++
    s!"mp prove {Sd}.writeItems.spec := by\n  \
  intro d dl pos n a\n  \
  vcgen [{S}.writeItems] invariants\n  \
  · fun done _ (_, dd, p, _) => WItemsInv {F} {S}.toVal {sz} dl.toNat a d pos (min done.length n.toNat) dd p\n  \
  all_goals try dsimp only at *\n  \
  case vc1 hpre => exact WItemsInv.init hpre.2.2\n  \
  case vc2 hpre _ dd p _ hinv =>\n    \
    rw [List.length_range, Nat.min_eq_right hpre.1.2.1] at hinv\n    \
    exact hinv.done\n  \
  case vc3 hpre pref cur suff hr _ dd p _ hinv hc =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    rw [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega), {F}_maxSize]\n    \
    have := hinv.2.1\n    \
    refine ⟨⟨by omega, ?_⟩, hpre.2.1, hinv.2.2⟩\n    \
    simpa [vget, show pref.length < fmtM by omega] using hpre.1.2.2 pref.length (by omega) hc\n  \
  case vc4 hpre pref cur suff hr _ dd p _ hinv hc _ p' dd' _ hx =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    rw [UInt64.toNat_ofNat_of_lt' (show pref.length < 2 ^ 64 by omega)] at hx\n    \
    simp only [List.length_append, List.length_singleton,\n      \
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)]\n    \
    exact hinv.call (by omega) hx\n  \
  case vc5 hpre pref cur suff hr _ dd p _ hinv hc =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    rw [List.length_range, Nat.min_eq_right (by omega)]\n    \
    rw [Nat.min_eq_right (by omega)] at hinv\n    \
    exact hinv"),
   (s!"the proof of the element writer's obligations `{S}.writeItems.safe`", preamble ++
    s!"mp prove {Sd}.writeItems.safe := by\n  \
  mp_auto [{F}_maxSize, vget, WrittenT, Writes.isFull] invariants\n  \
  · fun done _ (_, dd, p, _) => p.toNat ≤ pos.toNat + (min done.length n.toNat) * {sz} ∧\n      \
      ∀ k < d.len.toNat, dd.isFull k = true"),
   ("the section of the generated code", "end")]

/-- The element validator of a structure `S` with the format `F`, for at most `m` elements. -/
def validItemsText (S Sd F : Name) (m : Nat) : List (String × String) :=
  [("the section of the generated code", "section"),
   ("the section of the generated code", "variable (fmtN : Nat) (fmtHN : fmtN < 2 ^ 64)"),
   ("the section of the generated code", "include fmtHN"),
   (s!"the element validator `{S}.validItems_{m}`", preamble ++
    s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
    /-- Check `n ≤ {m}` values of `{S}` one after another. -/\n\
    mp def {Sd}.validItems_{m} (s : &[UInt8; fmtN]) (pos : &mut UInt64) (n : UInt64)\n    \
      requires pos.toNat ≤ s.len.toNat ∧ n.toNat ≤ {m}\n    \
      ensures ItemsC {F} (Slots.bytes s s.len.toNat) pos n.toNat result pos' ∧\n      \
        (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do\n  \
    let mut good := true\n  \
    for i in 0...{m} do\n    \
      if i ≥ n then break\n    \
      if good then\n      \
        good := {S}.validAt (&s) (&mut pos)\n  \
    good"),
   (s!"the proof of the element validator's contract `{S}.validItems_{m}.spec`", preamble ++
    s!"mp prove {Sd}.validItems_{m}.spec := by\n  \
  intro s sl pos n\n  \
  vcgen [{S}.validItems_{m}] invariants\n  \
  · fun done _ (good, p, _) => CItemsInv {F} (Slots.bytes s sl.toNat) pos (min done.length n.toNat) good p\n  \
  all_goals try dsimp only at *\n  \
  case vc1 hpre => exact CItemsInv.init (by simpa using hpre.1.1)\n  \
  case vc2 hpre good p _ hinv =>\n    \
    rw [List.length_range, Nat.min_eq_right hpre.1.2] at hinv\n    \
    simpa using hinv.done\n  \
  case vc3 hpre pref cur suff hr good p _ hinv hc hg =>\n    \
    subst hg; exact ⟨by simpa using hinv.pos_le, hpre.2⟩\n  \
  case vc4 hpre pref cur suff hr good p _ hinv hc hg ok p' _ hx =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    subst hg\n    \
    simp only [List.length_append, List.length_singleton,\n      \
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)]\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    exact hinv.call (by simpa using hpre.1.1) hx.1 (by simpa using hx.2)\n  \
  case vc5 hpre pref cur suff hr good p _ hinv hc hg =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    simp only [Bool.not_eq_true] at hg; subst hg\n    \
    simp only [List.length_append, List.length_singleton,\n      \
      Nat.min_eq_left (show pref.length + 1 ≤ n.toNat by omega)]\n    \
    rw [Nat.min_eq_left (by omega)] at hinv\n    \
    exact hinv.skip\n  \
  case vc6 hpre pref cur suff hr good p _ hinv hc =>\n    \
    obtain ⟨rfl, _⟩ := range_split hr\n    \
    rw [Lib.Slice.ofNat_lt_iff _ (by omega)] at hc\n    \
    rw [List.length_range, Nat.min_eq_right (by omega)]\n    \
    rw [Nat.min_eq_right (by omega)] at hinv\n    \
    exact hinv"),
   (s!"the proof of the element validator's obligations `{S}.validItems_{m}.safe`", preamble ++
    s!"mp prove {Sd}.validItems_{m}.safe := by\n  \
  mp_auto invariants\n  \
  · fun _ _ (good, p, _) => good = true → p.toNat ≤ s.len.toNat"),
   ("the section of the generated code", "end")]

/-- The generated commands' text, by what each defines. -/
def genText (T Tdecl fName fFull : Name) (ns : List Node) (seed : Nat) (doc : String) :
    List (String × String) :=
  let maxSize := maxSizeOf ns
  let bs := boundsOf ns
  let seqDefs := if (arraysOf ns).isEmpty then [] else
    ["Millipede.Format.Seq.toValWith", "Millipede.Format.Seq.items", "Millipede.Format.Seq.Bound"]
  let unfoldP := ", ".intercalate ([s!"{fName}", s!"{T}.toVal", s!"{T}.Bound"] ++
    (leafNames ns).eraseDups ++ seqDefs)
  let unfoldV := ", ".intercalate ([s!"{fName}"] ++ (leafNames ns).eraseDups)
  let lenses := (usedFields ns).eraseDups.map (fun x => s!"{T}.{x}.lens_get") ++
    (if (arraysOf ns).isEmpty then [] else
      ["Millipede.Format.Seq.len.lens_get", "Millipede.Format.Seq.data.lens_get"])
  let seqDefs := seqDefs ++ lenses
  let maxW := ", ".intercalate ([s!"{fName}_maxSize"] ++
    (subsOf ns).map fun i => s!"{i.fmtName}_maxSize")
  let pbody := ((parseStmts seed "  " ns).run' (0, false)).run
  let wbody := ((writeStmts "  " ns).run' 0).run
  let vbody := ((validStmts "  " ns).run' 0).run
  let wbody := if wbody.isEmpty then ["  return ()"] else wbody
  [(s!"the description `{fName}`",
    s!"{doc}def {fName} : Millipede.Format.Fmt :=\n  {fmtText ns}"),
   (s!"`{fName}_maxSize`",
    s!"/-- The largest number of bytes of a value of `{fName}`. -/\n\
      theorem {fName}_maxSize : {fName}.maxSize = {maxSize} := rfl"),
   (s!"`{T}.toVal`",
    s!"/-- The value of `{fName}` that a `{T}` stands for. -/\n\
      def {Tdecl}.toVal (r : {T}) : Millipede.Format.Val :=\n  {valText ns}"),
   (s!"`{T}.Bound`",
    s!"/-- The byte strings of a `{T}` are within the bounds of `{fName}`. -/\n\
      def {Tdecl}.Bound (r : {T}) : Prop :=\n  {if bs.isEmpty then "True" else " ∧ ".intercalate bs}"),
   ("the section of the generated code", "section"),
   ("the section of the generated code", "variable (fmtN : Nat) (fmtHN : fmtN < 2 ^ 64)"),
   ("the section of the generated code", "include fmtHN"),
   (s!"the parser `{T}.parseAt`", preamble ++
      s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
      /-- Parse a `{T}` of the format `{fName}` at `pos`. -/\n\
      mp def {Tdecl}.parseAt (s : &[UInt8; fmtN]) (pos : &mut UInt64) (out : &mut {T})\n    \
        requires pos.toNat ≤ s.len.toNat\n    \
        ensures Parsed {fFull} (Slots.bytes s s.len.toNat) pos result pos' out'.toVal ∧\n      \
          (result = true → pos'.toNat ≤ s.len.toNat ∧ {T}.Bound out') : Bool := do\n" ++
        "\n".intercalate pbody),
   (s!"the writer `{T}.writeAt`", preamble ++
      s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
      /-- Write a `{T}` in the format `{fName}` at `pos`. -/\n\
      mp def {Tdecl}.writeAt (d : &mut [UInt8; fmtN]) (pos : &mut UInt64) (v : &{T})\n    \
        requires pos.toNat + {fFull}.maxSize ≤ d.len.toNat ∧ {T}.Bound v\n    \
        ensures Written {fFull} d d' pos pos' v.toVal ∧ pos'.toNat ≤ pos.toNat + {maxSize} : \
          Unit := do\n" ++
        "\n".intercalate wbody),
   (s!"the validator `{T}.validAt`", preamble ++
      s!"set_option mp.autoSafe false in\nset_option mp.autoSpec false in\n\
      /-- Check that a value of the format `{fName}` is at `pos`, and move past it. -/\n\
      mp def {Tdecl}.validAt (s : &[UInt8; fmtN]) (pos : &mut UInt64)\n    \
        requires pos.toNat ≤ s.len.toNat\n    \
        ensures Checked {fFull} (Slots.bytes s s.len.toNat) pos result pos' ∧\n      \
          (result = true → pos'.toNat ≤ s.len.toNat) : Bool := do\n" ++
        "\n".intercalate vbody),
   (s!"the proof of the validator's contract `{T}.validAt.spec`", preamble ++
      s!"mp prove {Tdecl}.validAt.spec := by\n  intros\n  vcgen [{T}.validAt]\n  \
        all_goals fmt_norm\n  all_goals try simp only [{unfoldV}, ← UInt64.toNat_inj, UInt64.reduceToNat]\n  \
        all_goals fmt_close"),
   (s!"the proof of the validator's obligations `{T}.validAt.safe`", preamble ++
      s!"set_option maxHeartbeats 8000000 in\nmp prove {Tdecl}.validAt.safe := by\n  fmt_safe [{", ".intercalate ([s!"{fName}"] ++ lenses)}]"),
   (s!"the proof of the parser's contract `{T}.parseAt.spec`", preamble ++
      s!"mp prove {Tdecl}.parseAt.spec := by\n  intros\n  vcgen [{T}.parseAt]\n  \
        all_goals fmt_norm\n  all_goals try simp only [{unfoldP}, ← UInt64.toNat_inj, UInt64.reduceToNat]\n  \
        all_goals fmt_close"),
   (s!"the proof of the parser's obligations `{T}.parseAt.safe`", preamble ++
      s!"set_option maxHeartbeats 8000000 in\nmp prove {Tdecl}.parseAt.safe := by\n  fmt_safe [{", ".intercalate ([s!"{T}.Bound"] ++ seqDefs)}]"),
   (s!"the proof of the writer's contract `{T}.writeAt.spec`", preamble ++
      s!"mp prove {Tdecl}.writeAt.spec := by\n  intros\n  vcgen [{T}.writeAt]\n  \
        all_goals fmt_norm\n  all_goals try simp only [{maxW}] at *\n  \
        all_goals try simp only [{unfoldP}, ← UInt64.toNat_inj, UInt64.reduceToNat] at *\n  \
        all_goals fmt_split\n  all_goals fmt_close"),
   (s!"the proof of the writer's obligations `{T}.writeAt.safe`", preamble ++
      s!"set_option maxHeartbeats 8000000 in\nmp prove {Tdecl}.writeAt.safe := by\n  fmt_safe [{", ".intercalate ([maxW, s!"{T}.Bound"] ++ seqDefs)}]"),
   ("the section of the generated code", "end")]

@[command_elab mpFormat] def elabMpFormat : CommandElab := fun stx => do
  let fName := stx[3].getId
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[5]
  let ns ← recOf stx[7]
  let fs ← fieldsOf T
  (checkNodes stx T fs ns).run' []
  let used := usedFields ns
  for (f, _) in fs do
    unless used.contains f do
      throwErrorAt stx[5] "mp format: the field `{f}` of `{T}` is not in the description"
  let seed := mp.format.seedBug.get (← getOptions)
  let fFull := (← getCurrNamespace) ++ fName
  let doc := match stx[0].getOptional? with
    | some d => d.reprint.getD ""
    | none => s!"/-- The format of `{T}`. -/\n"
  let curNs ← getCurrNamespace
  let Tdecl := if curNs.isPrefixOf T then T.replacePrefix curNs .anonymous else `_root_ ++ T
  let declOf (n : Name) : Name :=
    if curNs.isPrefixOf n then n.replacePrefix curNs .anonymous else `_root_ ++ n
  -- The element loops of the repetitions' structures, generated once for each.
  let mut pre : List (String × String) := []
  let mut done : List Name := []
  for (S, i, m) in arraysOf ns do
    let env ← getEnv
    unless env.contains (S ++ `parseItems) || done.contains S do
      pre := pre ++ itemsText S (declOf S) i.fmtName i.maxSize
      done := S :: done
    let vn := S ++ Name.mkSimple s!"validItems_{m}"
    unless env.contains vn || pre.any (·.1.endsWith s!"`{vn}`") do
      pre := pre ++ validItemsText S (declOf S) i.fmtName m
  let cmds := pre ++ genText T Tdecl fName fFull ns seed doc
  -- When a generated command fails, the environment and the scopes are those before the
  -- command, so that nothing of a rejected description is left.
  let env0 ← getEnv
  let scopes0 := (← get).scopes
  try
    for (what, src) in cmds do
      runGen stx what src
  catch e =>
    setEnv env0
    modify fun st => { st with scopes := scopes0 }
    throw e
  modifyEnv (formatExt.addEntry · { struct := T, fmtName := fFull, maxSize := maxSizeOf ns })

end Millipede.Meta.Format
