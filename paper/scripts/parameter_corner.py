"""Exact parameter-corner, cutoff and dimensional calculations for the paper.

Everything is computed from exact rationals (fractions) and converted to
floating point only for display.  Run with the repository interpreter:

    python scripts/parameter_corner.py

Writes data/parameter_corner.json next to this package.
"""
from __future__ import annotations

import json
import math
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "data"

# Certified constants (Lean: SharpRecovery.deadline_sharp, witness_time_lower_sharp).
UPPER = F(31, 10)          # T_all <= UPPER / (p^2 h^7)
LOWER = F(400, 1313)       # T_witness >= LOWER / (p^2 h^7)
OLD_UPPER, OLD_LOWER = F(7), F(1, 28)
NA = 602214076000000000000000  # exact SI Avogadro constant, mol^-1

def case(label: str, h: F, u: F) -> dict:
    p = h * u
    lam = p * p * h**7
    sx, sy, sz = p * h**3, p * h**2, p * h
    one_over_lam = 1 / lam
    bounds = {
        "x": [F(3, 64) * sx, 5 * sx],
        "y": [F(1, 16) * sy, 3 * sy],
        "z": [F(1, 8) * sz, sz],
    }
    counts = {k: [float(v[0] * NA), float(v[1] * NA)] for k, v in bounds.items()}
    # minimum inventory rise for the witness: W must increase by at least p h / 2
    inventory_rise_conc = p * h / 2
    inventory_rise_counts = inventory_rise_conc * NA  # at C0 = 1 mol/L, V = 1 L
    min_reverse3_events = math.ceil(inventory_rise_counts / 13)
    return {
        "label": label,
        "h": str(h), "u": str(u), "p": str(p),
        "epsilon": float(p * p),
        "pair3_reverse_rate": float(p * h**6),
        "one_over_p2h7": float(one_over_lam),
        "one_over_p2h7_exact": str(one_over_lam),
        "witness_lower_seconds": float(LOWER * one_over_lam),
        "deadline_upper_seconds": float(UPPER * one_over_lam),
        "previous_witness_lower_seconds": float(OLD_LOWER * one_over_lam),
        "previous_deadline_upper_seconds": float(OLD_UPPER * one_over_lam),
        "bounds_mol_per_litre": {k: [float(v[0]), float(v[1])] for k, v in bounds.items()},
        "molecule_counts_1L": counts,
        "reverse_rate_constants": {
            "pairs_1_2_L_per_mol_s": float(p * p),
            "pair_3_L_per_mol_s": float(p * h**6),
            "pair_4_per_s": float(p * p),
        },
        "log_cycle_ratio_1_over_4eps": float(-math.log(4 * float(p * p))),
        "witness_inventory_rise_mol_per_litre": float(inventory_rise_conc),
        "witness_min_reverse_pair3_events_1L": int(min_reverse3_events),
    }

def main() -> None:
    cases = [
        case("rectangle_corner", F(1, 600), F(1, 20)),
        case("reference_gamma1_original", F(1, 1000), F(1, 10**15)),
        case("reference_gamma1_improved", F(1, 600), F(1, 600**5)),
    ]
    gamma_star = 0.5 + 3 * math.log(600) / math.log(12000)
    ratio = UPPER / LOWER
    # sanity: the sequential numerator at h = 1/600
    h = F(1, 600)
    numerator = 2 * h**7 + 32 * h**4 + F(40, 13)
    assert numerator < UPPER
    out = {
        "constants": {
            "deadline_constant": str(UPPER),
            "witness_constant": str(LOWER),
            "witness_constant_float": float(LOWER),
            "ratio_upper_over_lower": str(ratio),
            "ratio_float": float(ratio),
            "previous_ratio": float(OLD_UPPER / OLD_LOWER),
            "sequential_numerator_at_h_1_600": float(numerator),
            "sequential_numerator_exact": str(numerator),
        },
        "best_corner": {
            "gamma_star": gamma_star,
            "epsilon_max_over_rectangle": float(F(1, 144000000)),
            "statement": "p<=1/12000 forces epsilon=p^2<=1/144000000; the exponent family reaches this corner at gamma_star",
        },
        "cutoffs": {
            "gamma1_original_log10": -36.0,
            "gamma1_improved_log10": -12 * math.log10(600),
            "gamma2_improved_log10": max(-12 * math.log10(600) / 3, -12 * math.log10(20) / 3),
        },
        "cases": cases,
        "units": {"C0_mol_per_litre": 1, "tau0_seconds": 1, "V_litres": 1, "N_A": NA},
    }
    DATA.mkdir(exist_ok=True)
    (DATA / "parameter_corner.json").write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    for c in cases:
        print(c["label"], "1/(p^2h^7)=%.5e" % c["one_over_p2h7"],
              "T_w>=%.5e s" % c["witness_lower_seconds"], "T_all<=%.5e s" % c["deadline_upper_seconds"],
              "x_upper_count=%.4g" % c["molecule_counts_1L"]["x"][1],
              "min_rev3_events=%.3e" % c["witness_min_reverse_pair3_events_1L"])
    print("gamma_star=%.10f ratio=%s=%.5f numerator=%.12f" % (gamma_star, ratio, float(ratio), float(numerator)))

if __name__ == "__main__":
    main()
