from profile_lake.transform import parse_and_transform_lean, revert_transform_lean

def test_theorem_with_kernel_decide():
    src = """theorem mapInc_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    readNatList (runAdd mapInc_term (natList l)) = mapInc l :=
  forall_small (fun l => readNatList (runAdd mapInc_term (natList l)) = mapInc l) (by decide +kernel) l hlen hx
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] theorem mapInc_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd mapInc_term (natList l)) = mapInc l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => readNatList (runAdd mapInc_term (natList l)) = mapInc l) (by decide +kernel) l hlen hx
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
    assert revert_transform_lean(res) == src


def test_consecutive_theorems_with_kernel_decide():
    src = """theorem mapInc_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    readNatList (runAdd mapInc_term (natList l)) = mapInc l :=
  forall_small (fun l => readNatList (runAdd mapInc_term (natList l)) = mapInc l) (by decide +kernel) l hlen hx

theorem sumFoldl_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
    runAdd sumFoldl_term (natList l) = sumFoldl l :=
  forall_small (fun l => runAdd sumFoldl_term (natList l) = sumFoldl l) (by decide +kernel) l hlen hx
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] theorem mapInc_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     readNatList (runAdd mapInc_term (natList l)) = mapInc l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => readNatList (runAdd mapInc_term (natList l)) = mapInc l) (by decide +kernel) l hlen hx

-- [SKIPPED BY PROFILE_LAKE] theorem sumFoldl_term_small (l : List Nat) (hlen : l.length ≤ 3) (hx : ∀ x ∈ l, x < 4) :
-- [SKIPPED BY PROFILE_LAKE]     runAdd sumFoldl_term (natList l) = sumFoldl l :=
-- [SKIPPED BY PROFILE_LAKE]   forall_small (fun l => runAdd sumFoldl_term (natList l) = sumFoldl l) (by decide +kernel) l hlen hx
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
    assert revert_transform_lean(res) == src

def test_standalone_guard_single_line():
    src = """#guard #![1, 2, 3].head = 1\n#guard #![1, 2, 3].tail = #[2, 3]\n"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] #guard #![1, 2, 3].head = 1\n-- [SKIPPED BY PROFILE_LAKE] #guard #![1, 2, 3].tail = #[2, 3]\n"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
    assert revert_transform_lean(res) == src


def test_guard_msgs_wrapping_eval_is_skipped_completely():
    src = """/--
info: LeanScript.Ty.shape
      rest := [] })
-/
#guard_msgs in
#eval (Ty.record ⟨.prim .nat, .self, []⟩ : Ty)

example : Nat := 1
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] /--
-- [SKIPPED BY PROFILE_LAKE] info: LeanScript.Ty.shape
-- [SKIPPED BY PROFILE_LAKE]       rest := [] })
-- [SKIPPED BY PROFILE_LAKE] -/
-- [SKIPPED BY PROFILE_LAKE] #guard_msgs in
-- [SKIPPED BY PROFILE_LAKE] #eval (Ty.record ⟨.prim .nat, .self, []⟩ : Ty)

example : Nat := 1
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
    assert revert_transform_lean(res) == src


def test_guard_msgs_wrapping_example_is_never_touched():
    src = """/--
error: ty_wf: the declaration being defined occurs to the left of an arrow, which no type of the language does
-/
#guard_msgs in
example : Ty.Wf (.recAlias (.fn .self (.prim .nat))) := by ty_wf
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is False
    assert res == src


def test_multiline_eval_block():
    src = """#eval do
  let x := 10
  let y := 20
  IO.println (x + y)

def nextDef : Nat := 42
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] #eval do
-- [SKIPPED BY PROFILE_LAKE]   let x := 10
-- [SKIPPED BY PROFILE_LAKE]   let y := 20
-- [SKIPPED BY PROFILE_LAKE]   IO.println (x + y)

def nextDef : Nat := 42
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
    assert revert_transform_lean(res) == src


def test_mixed_guards_and_theorems():
    src = """#guard fib (ofNat 10) = 55
#guard fibTR (ofNat 10) = 55

/-- The Peano `fib` is the `fib` of `TermTests.FibWindow`. -/
theorem fib_ofNat : (n : Nat) → fib (ofNat n) = TermTests.FibWindow.fib n
  | 0 => rfl
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] #guard fib (ofNat 10) = 55
-- [SKIPPED BY PROFILE_LAKE] #guard fibTR (ofNat 10) = 55

/-- The Peano `fib` is the `fib` of `TermTests.FibWindow`. -/
theorem fib_ofNat : (n : Nat) → fib (ofNat n) = TermTests.FibWindow.fib n
  | 0 => rfl
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected


def test_guard_with_nested_parentheses():
    src = """#guard (nes!"112" > nes!"11")
#guard if (nes!"112" < nes!"11") then true else true
"""
    expected = """-- [SKIPPED BY PROFILE_LAKE] #guard (nes!"112" > nes!"11")
-- [SKIPPED BY PROFILE_LAKE] #guard if (nes!"112" < nes!"11") then true else true
"""
    res, changed = parse_and_transform_lean(src)
    assert changed is True
    assert res == expected
