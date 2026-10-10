"""Vector figures for the paper.

    python scripts/make_figures.py

Reads data/recovery_trajectory.npz (saved from Radau on the complete transformed ODE at
h=1/600, u=1/20, nominal prefactors, exact slow time tau = p^2 h^7 t) and
writes figures/*.pdf.  No new integration is performed here.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
import numpy as np

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
FIG = PKG / "figures"
DATA = PKG / "data"
FIG.mkdir(exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9,
    "axes.spines.top": False,
    "axes.spines.right": False,
    "pdf.fonttype": 42,
    "mathtext.fontset": "cm",
})
BLUE, GREEN, RUST, VIOLET, GRAY = "#23556b", "#438b63", "#a54e38", "#6d5898", "#777777"
LOWER, UPPER = 400 / 1313, 3.1


def exponent_figure() -> None:
    g = np.linspace(0.55, 3.45, 400)
    fig, axes = plt.subplots(1, 2, figsize=(6.6, 2.6))
    ax = axes[0]
    for q, lab, col in [((2 * g + 1) / 4, r"$x$: $(2\gamma+1)/4$", BLUE),
                        ((g + 1) / 3, r"$y$: $(\gamma+1)/3$", GREEN),
                        ((2 * g + 5) / 12, r"$z$: $(2\gamma+5)/12$", RUST),
                        ((14 * g + 5) / 12, r"recovery: $(14\gamma+5)/12$", VIOLET)]:
        ax.plot(g, q, color=col, lw=1.8, label=lab)
    ax.set_xlabel(r"reverse exponent $\gamma$")
    ax.set_ylabel("exponent")
    ax.set_xlim(0.5, 3.5)
    ax.legend(fontsize=7, frameon=False, loc="upper left")
    ax.grid(alpha=0.15)

    ax = axes[1]
    new = -np.maximum(12 * np.log10(600) / (2 * g - 1), 12 * np.log10(20) / (7 - 2 * g))
    old = -36 / np.minimum(2 * g - 1, 7 - 2 * g)
    ax.plot(g, new, color=BLUE, lw=1.8, label=r"$h\leq 1/600$, $u\leq 1/20$")
    ax.plot(g, old, color=GRAY, lw=1.3, ls="--", label=r"$h,u\leq 10^{-3}$")
    gstar = 0.5 + 3 * math.log(600) / math.log(12000)
    ax.plot([gstar], [math.log10(1 / 144e6)], "o", color=RUST, ms=5, zorder=5)
    ax.annotate(r"$\gamma_*\approx 2.543$", (gstar, math.log10(1 / 144e6)),
                xytext=(1.55, -60), fontsize=7.5, color=RUST,
                arrowprops=dict(arrowstyle="-", color=RUST, lw=0.8))
    ax.set_xlabel(r"reverse exponent $\gamma$")
    ax.set_ylabel(r"$\log_{10}\varepsilon_{\max}(\gamma)$")
    ax.set_xlim(0.5, 3.5)
    ax.set_ylim(-380, 10)
    ax.legend(fontsize=7, frameon=False, loc="lower center")
    ax.grid(alpha=0.15)
    fig.tight_layout()
    fig.savefig(FIG / "exponent_family.pdf", bbox_inches="tight")
    plt.close(fig)


def trajectory_figure() -> None:
    d = np.load(DATA / "recovery_trajectory.npz")
    tau, A, B, Q = d["tau"], d["A"], d["B"], d["Q"]
    rep = json.loads((DATA / "recovery_trajectory.json").read_text())
    tcap = rep["observed_sampled_capture_slow_time"]
    inside = (A >= 3.5) & (A <= 4.5) & (B >= 1.5) & (B <= 2.5) & (Q >= 0.5) & (Q <= 0.75)
    first = int(np.argmax(inside))
    assert abs(tau[first] - tcap) < 1e-9

    fig = plt.figure(figsize=(6.8, 4.6))
    gs = fig.add_gridspec(3, 2, width_ratios=[1.55, 1], hspace=0.35, wspace=0.3)
    panels = [("A", A, (3, 5), (3.5, 4.5), BLUE), ("B", B, (1, 3), (1.5, 2.5), GREEN),
              ("Q", Q, (0.25, 1), (0.5, 0.75), RUST)]
    for i, (name, vals, outer, inner, col) in enumerate(panels):
        ax = fig.add_subplot(gs[i, 0])
        ax.axhspan(*outer, color="#eeeeee", zorder=0)
        ax.axhspan(*inner, color="#d8e8dc", zorder=1)
        if name == "Q":
            ax.axvspan(0, LOWER, color=RUST, alpha=0.10, zorder=1, lw=0)
            ax.text(LOWER / 2, 0.93, "excluded for\nthe witness\n" + r"$\tau<400/1313$",
                    ha="center", va="top", fontsize=6.5, color=RUST)
        ax.plot(tau, vals, color=col, lw=1.7, zorder=3)
        ax.axvline(tcap, color="black", lw=1.1, ls="--", zorder=4)
        ax.set_ylabel(name)
        ax.set_xlim(0, 1.2)
        pad = 0.05 * (outer[1] - outer[0])
        ax.set_ylim(outer[0] - pad, outer[1] + pad)
        ax.grid(alpha=0.15)
        if i < 2:
            ax.tick_params(labelbottom=False)
        else:
            ax.set_xlabel(r"slow time $\tau=p^2h^7t$")
        if i == 0:
            ax.text(tcap + 0.02, 4.85, r"first sampled target entry $\tau\approx%.3f$" % tcap,
                    fontsize=7, va="top")
    # fast-time insets (log axis)
    mask = tau > 0
    for i, (name, vals, outer, inner, col) in enumerate(panels[:2]):
        ax = fig.add_subplot(gs[i, 1])
        ax.axhspan(*outer, color="#eeeeee", zorder=0)
        ax.axhspan(*inner, color="#d8e8dc", zorder=1)
        ax.semilogx(tau[mask], vals[mask], color=col, lw=1.7, zorder=3)
        ax.set_xlim(1e-22, 1.2)
        pad = 0.05 * (outer[1] - outer[0])
        ax.set_ylim(outer[0] - pad, outer[1] + pad)
        ax.set_ylabel(name)
        ax.grid(alpha=0.15)
        ax.tick_params(labelbottom=(i == 1))
        if i == 0:
            ax.set_title("fast transients (log scale)", fontsize=8)
        if i == 1:
            ax.set_xlabel(r"slow time $\tau$ (log)")
    ax = fig.add_subplot(gs[2, 1])
    ax.axis("off")
    ax.text(0.0, 0.9, "certified window for the witness\n"
            r"$400/1313\approx0.3046\leq\tau_{\rm entry}\leq 31/10$" "\n"
            "observed (sampled): %.3f\n"
            r"one slow unit $=4.03\times10^{27}$ s" % tcap,
            fontsize=7.5, va="top", ha="left", transform=ax.transAxes)
    fig.savefig(FIG / "recovery_trajectory.pdf", bbox_inches="tight")
    plt.close(fig)


def rectangle_figure() -> None:
    h = np.logspace(-6, math.log10(1 / 600), 220)
    u = np.logspace(-6, math.log10(1 / 20), 220)
    Hh, Uu = np.meshgrid(h, u)
    val = -np.log10(Uu**2 * Hh**9)  # log10 of 1/(p^2 h^7)
    fig, ax = plt.subplots(figsize=(3.6, 3.1))
    cs = ax.contourf(Hh, Uu, val, levels=18, cmap="viridis_r")
    cb = fig.colorbar(cs, ax=ax, pad=0.02)
    cb.set_label(r"$\log_{10}\,(p^2h^7)^{-1}$", fontsize=8)
    ax.set_xscale("log")
    ax.set_yscale("log")
    gstar = 0.5 + 3 * math.log(600) / math.log(12000)
    for gam, col, ls, lab in [(2.0, "white", ":", r"$\gamma=2$"), (gstar, RUST, "-", r"$\gamma_*\approx2.543$")]:
        # family path: log u / log h = (7-2g)/(2g-1); it passes through the corner only for gamma_*
        slope = (7 - 2 * gam) / (2 * gam - 1)
        hh = np.logspace(-6, math.log10(1 / 600), 50)
        uu = hh**slope
        keep = (uu <= 1 / 20) & (uu >= 1e-6)
        ax.plot(hh[keep], uu[keep], color=col, lw=1.8, ls=ls)
        mid = len(hh[keep]) // 2
        ax.annotate(lab, (hh[keep][mid], uu[keep][mid]), xytext=(4, -14), textcoords="offset points",
                    fontsize=7, color="black", bbox=dict(boxstyle="round,pad=0.2", fc="white", ec="none", alpha=0.85))
    ax.plot([1 / 600], [1 / 20], "o", color=RUST, ms=5)
    ax.set_xlabel(r"$h$")
    ax.set_ylabel(r"$u$")
    ax.set_title(r"recovery scale over the certified rectangle", fontsize=8)
    fig.tight_layout()
    fig.savefig(FIG / "parameter_rectangle.pdf", bbox_inches="tight")
    plt.close(fig)


if __name__ == "__main__":
    exponent_figure()
    trajectory_figure()
    rectangle_figure()
    print("figures written to", FIG)
