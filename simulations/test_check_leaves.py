"""Tests for the leaf detector.

The gate asks whether a module's theorems are *used* by another module. Its
first implementation asked something weaker — whether a token spelled like one
of the module's declarations occurs anywhere in the tree — and the two answers
differ in three ways, each of which is a regression below:

* a **namespace collision**: `Network.run` in one module and `Trajectory.run`
  in another are different constants that share a final segment;
* a **qualified declaration**: `Widget.ofThing` declared in one module is not
  the structure `Widget` declared in the module it extends;
* a **reverse dependency**: a file that `A` imports cannot be a consumer of
  `A`, whatever tokens it contains — the reference would not resolve.

All three make a leaf look consumed, which is the direction that matters: the
gate exists to find dead modules, and a false consumer hides one.
"""

import tempfile
import unittest
from pathlib import Path

import check_leaves


class LeanTreeTest(unittest.TestCase):
    """Each test builds a small Lean package and asks which modules are leaves."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        self.lean_dir = Path(self._tmp.name) / "Pkg"
        self.lean_dir.mkdir()

    def write(self, name: str, body: str) -> Path:
        path = self.lean_dir / f"{name}.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(body, encoding="utf-8")
        return path

    def leaf_names(self) -> list[str]:
        return [mod.name for mod in check_leaves.find_leaves(self.lean_dir)]


class FalseConsumerTest(LeanTreeTest):
    def test_a_shared_final_segment_is_not_a_reference(self) -> None:
        """`Network.run` and `Trajectory.run` are two constants, not one."""
        self.write(
            "A",
            "namespace Pkg.Network\ndef run (c : Nat) : Nat := c\nend Pkg.Network\n",
        )
        self.write(
            "B",
            "namespace Pkg.Trajectory\ndef run (c : Nat) : Nat := c\n"
            "def twice (c : Nat) : Nat := run (run c)\nend Pkg.Trajectory\n",
        )

        self.assertEqual(self.leaf_names(), ["A.lean", "B.lean"])

    def test_a_namespace_prefix_is_not_the_declaration(self) -> None:
        """`Widget.ofThing` lives in `Widget`'s namespace; it is not `Widget`."""
        self.write(
            "A", "import Pkg.B\nnamespace Pkg\ndef Widget.ofThing : Widget := ⟨0⟩\nend Pkg\n"
        )
        self.write("B", "namespace Pkg\nstructure Widget where\n  size : Nat\nend Pkg\n")

        self.assertIn("A.lean", self.leaf_names())

    def test_an_imported_module_is_not_a_consumer_of_its_importer(self) -> None:
        """B cannot reference A's constants: the import runs the other way."""
        self.write("A", "import Pkg.B\nnamespace Pkg\ndef gadget : Nat := widget\nend Pkg\n")
        self.write(
            "B",
            "namespace Pkg\ndef widget : Nat := 0\ndef gadget' : Nat := widget\nend Pkg\n",
        )

        self.assertEqual(self.leaf_names(), ["A.lean"])


class RealConsumerTest(LeanTreeTest):
    def test_an_importer_that_uses_a_declaration_is_a_consumer(self) -> None:
        self.write("A", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")
        self.write("B", "import Pkg.A\nnamespace Pkg\ndef gadget : Nat := widget\nend Pkg\n")

        self.assertEqual(self.leaf_names(), ["B.lean"])

    def test_consumption_passes_through_a_transitive_import(self) -> None:
        """Lean makes A's constants visible in C through B; so does the gate."""
        self.write("A", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")
        self.write("B", "import Pkg.A\nnamespace Pkg\ndef spacer : Nat := 1\nend Pkg\n")
        self.write("C", "import Pkg.B\nnamespace Pkg\ndef gadget : Nat := widget\nend Pkg\n")

        self.assertEqual(self.leaf_names(), ["B.lean", "C.lean"])

    def test_a_qualified_reference_is_a_consumer(self) -> None:
        self.write("A", "namespace Pkg\ndef Widget.ofThing : Nat := 0\nend Pkg\n")
        self.write(
            "B",
            "import Pkg.A\nnamespace Pkg\ndef gadget : Nat := Widget.ofThing\nend Pkg\n",
        )

        self.assertEqual(self.leaf_names(), ["B.lean"])

    def test_dot_notation_on_a_term_is_a_consumer(self) -> None:
        """`N.run` elaborates to `Network.run N`; the token carries the segment."""
        self.write(
            "A",
            "namespace Pkg\nstructure Network where\n  size : Nat\n"
            "def Network.run (N : Network) : Nat := N.size\nend Pkg\n",
        )
        self.write(
            "B",
            "import Pkg.A\nnamespace Pkg\ndef gadget (N : Network) : Nat := N.run\nend Pkg\n",
        )

        self.assertEqual(self.leaf_names(), ["B.lean"])

    def test_an_ambiguous_final_segment_is_not_consumption(self) -> None:
        """Two visible constants share the segment, so the bare token resolves to
        neither; a consumer has to say which one it means."""
        self.write("A", "namespace Pkg.Network\ndef run : Nat := 0\nend Pkg.Network\n")
        self.write("B", "namespace Pkg.Trajectory\ndef run : Nat := 1\nend Pkg.Trajectory\n")
        self.write(
            "C",
            "import Pkg.A\nimport Pkg.B\nnamespace Pkg\ndef gadget : Nat := run\nend Pkg\n",
        )

        self.assertEqual(self.leaf_names(), ["A.lean", "B.lean", "C.lean"])


class ExclusionTest(LeanTreeTest):
    def test_prose_is_not_consumption(self) -> None:
        """A name discussed in a docstring and unused in code is C1's state."""
        self.write("A", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")
        self.write("B", "import Pkg.A\n/-! `widget` is discussed here. -/\n-- and here: widget\n")

        self.assertEqual(self.leaf_names(), ["A.lean"])

    def test_a_witness_is_not_a_consumer(self) -> None:
        """Witnesses import what they inhabit; presence is not usage."""
        self.write("A", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")
        self.write("Examples", "import Pkg.Examples.One\n")
        self.write(
            "Examples/One",
            "import Pkg.A\nnamespace Pkg\ndef instance' : Nat := widget\nend Pkg\n",
        )

        self.assertEqual(self.leaf_names(), ["A.lean"])

    def test_a_module_with_no_declarations_is_not_a_leaf(self) -> None:
        self.write("A", "import Pkg.B\n/-! Prose only. -/\n")
        self.write("B", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")

        self.assertEqual(self.leaf_names(), ["B.lean"])

    def test_the_not_checked_modules_are_skipped(self) -> None:
        """`Chain.lean` is the top composition module: nothing consumes it."""
        self.write("Chain", "import Pkg.A\nnamespace Pkg\ndef chain : Nat := widget\nend Pkg\n")
        self.write("A", "namespace Pkg\ndef widget : Nat := 0\nend Pkg\n")

        self.assertEqual(self.leaf_names(), [])


class DeclarationTest(unittest.TestCase):
    def test_a_declaration_carries_its_enclosing_namespaces(self) -> None:
        code = "namespace Pkg\nnamespace Inner\ndef widget : Nat := 0\nend Inner\nend Pkg\n"

        self.assertEqual(check_leaves.declarations(code), {"Pkg.Inner.widget"})

    def test_a_dotted_declaration_keeps_its_own_prefix(self) -> None:
        code = "namespace Pkg\n@[simp] theorem Widget.ofThing_size : True := trivial\nend Pkg\n"

        self.assertEqual(check_leaves.declarations(code), {"Pkg.Widget.ofThing_size"})

    def test_an_unnamed_section_end_does_not_close_a_namespace(self) -> None:
        code = "namespace Pkg\nsection\nvariable (n : Nat)\nend\ndef widget : Nat := 0\nend Pkg\n"

        self.assertEqual(check_leaves.declarations(code), {"Pkg.widget"})

    def test_the_resolvable_forms_of_a_name_are_its_suffixes(self) -> None:
        self.assertEqual(
            check_leaves.suffixes("Pkg.Widget.ofThing"),
            ["Pkg.Widget.ofThing", "Widget.ofThing", "ofThing"],
        )


class BaselineTest(unittest.TestCase):
    def test_a_recorded_leaf_that_gained_a_consumer_fails(self) -> None:
        unrecorded, stale = check_leaves.classify([], {"Gone.lean": "reason"})

        self.assertEqual(unrecorded, [])
        self.assertEqual(stale, ["Gone.lean"])

    def test_an_unrecorded_leaf_fails(self) -> None:
        unrecorded, stale = check_leaves.classify([Path("New.lean")], {})

        self.assertEqual([mod.name for mod in unrecorded], ["New.lean"])
        self.assertEqual(stale, [])

    def test_the_lean_development_matches_its_recorded_baseline(self) -> None:
        """The gate on the real tree, which is what runs on commit."""
        self.assertEqual(check_leaves.main(), 0)


if __name__ == "__main__":
    unittest.main()
