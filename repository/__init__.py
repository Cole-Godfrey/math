"""index and audit kernel-checked mathematical declarations."""

import sys


# kernel natural literals have no decimal digit bound.
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
