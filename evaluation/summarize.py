#!/usr/bin/env python3
"""Rebuild the evaluation tables from the JSON models in results/.

Usage:
    python3 evaluation/summarize.py [results-dir]

Reads nothing but the deposited models, so it reproduces the reported counts
without re-running discovery.
"""
import json
import os
import sys

LOGS = [
    ("Order Management", "order-management"),
    ("Container Logistics", "container-logistics"),
    ("P2P", "p2p"),
    ("SLURM", "slurm"),
    ("BPIC2017", "bpic2017"),
]
RHOS = ["0", "0.1", "0.2"]


def load(root, log, name):
    path = os.path.join(root, log, name)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        d = json.load(f)
    return d if isinstance(d, list) else d["arcs"]


def size(arcs):
    return "-" if arcs is None else len(arcs)


def without_flat_counterpart(arcs):
    """Arcs that no per-type flattening can express: two or more involved types,
    or at least one type involved as All."""
    n = 0
    for a in arcs:
        label = a["label"]
        involved = len(label["each"]) + len(label["any"]) + len(label["all"])
        if involved >= 2 or label["all"]:
            n += 1
    return n


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "results"
    )

    print("Model sizes (paper Table 2).  exist = existence model at rho = 0.2,")
    print("N = discovered negative model, down = reduced under fixed premises,")
    print("down* = reduced under matched thresholds.\n")
    head = f"{'Log':<20}{'exist':>7}{'down':>6}"
    for rho in RHOS:
        head += f"{'N@' + rho:>9}{'down@' + rho:>9}{'down*@' + rho:>10}"
    print(head)
    for name, log in LOGS:
        row = f"{name:<20}"
        row += f"{size(load(root, log, 'existence.json')):>7}"
        row += f"{size(load(root, log, 'existence-reduced-rho0.2.json')):>6}"
        for rho in RHOS:
            row += f"{size(load(root, log, f'negative-discovered-rho{rho}.json')):>9}"
            row += f"{size(load(root, log, f'negative-reduced-fixed-rho{rho}.json')):>9}"
            row += f"{size(load(root, log, f'negative-reduced-matched-rho{rho}.json')):>10}"
        print(row)

    print("\nRetained arcs with no case-centric counterpart, of all retained arcs")
    print("(fixed premises).\n")
    print(f"{'Log':<20}" + "".join(f"{'rho=' + rho:>12}" for rho in RHOS))
    for name, log in LOGS:
        row = f"{name:<20}"
        for rho in RHOS:
            arcs = load(root, log, f"negative-reduced-fixed-rho{rho}.json")
            cell = "-" if arcs is None else f"{without_flat_counterpart(arcs)}/{len(arcs)}"
            row += f"{cell:>12}"
        print(row)


if __name__ == "__main__":
    main()
