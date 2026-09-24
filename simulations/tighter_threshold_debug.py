import numpy as np
from pathlib import Path
from dynamic_ramp_analysis import replica_escape_couplings

FIGURE_DIR = Path(__file__).resolve().parent / "figures"
SPEEDS = (0.1, 0.02, 0.01, 0.005, 0.002, 0.001, 0.0002, 0.0001)

speeds = []
delays: list[float] = []
for speed in SPEEDS:
    path = FIGURE_DIR / f"dynamic_ramp_replicas_v{speed:.0e}.npz"
    with np.load(path, allow_pickle=False) as saved:
        coupling = np.asarray(saved["coupling"])
        order_replicas = np.asarray(saved["order_replicas"])
    escape = replica_escape_couplings(coupling, order_replicas, 0.05, 3)
    finite = escape[np.isfinite(escape)]
    if finite.size == 32:
        speeds.append(speed)
        delay = finite - 2.0
        print(f"v={speed}: min delay = {np.min(delay):.4f}, mean = {np.mean(delay):.4f}")
