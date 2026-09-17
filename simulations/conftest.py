"""Hypothesis settings for the copy of this suite that ``mutmut`` runs.

``mutmut`` copies this directory into ``mutants/`` and drives pytest in-process,
forking a fresh child per mutant, so one test function is executed by many
different executors and under code that a mutation may have made arbitrarily
slow. Hypothesis reads both of those as faults in the test: ``differing_executors``
fires on the first, and the per-example deadline fires on the second. Neither
says anything about the mutant, and a mutant that dies of a spurious health-check
error is scored as killed by a test that never actually distinguished it.

The relaxation is therefore scoped to the mutants tree by the directory this file
is running from. The suite proper keeps Hypothesis at full strictness: a deadline
breach or a differing executor there is a real finding, and silencing it
everywhere to buy a clean mutation run would trade the stronger signal for the
weaker one.
"""

from pathlib import Path

from hypothesis import HealthCheck, settings

if Path(__file__).resolve().parent.name == "mutants":
    settings.register_profile(
        "mutmut",
        suppress_health_check=[HealthCheck.differing_executors],
        deadline=None,
    )
    settings.load_profile("mutmut")
