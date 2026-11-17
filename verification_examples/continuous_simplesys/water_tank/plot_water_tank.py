import pandas as pd
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pd.read_csv(
    os.path.join(path, "resultstank.csv"),
    header=None,
    names=["level"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

fig = plt.figure(figsize=(12, 7))

# Position
plt.plot(t, data["level"], label="system output")

plt.ylabel("Level")
plt.xlabel("Time (s)")
plt.grid(True)
plt.legend()

# Titre
fig.suptitle("Continuous evolution of a water tank", fontsize=16)

plt.tight_layout()

# Sauvegarde image
plt.savefig(
    os.path.join(path, "results_watertank.png"),
    dpi=300,
    bbox_inches="tight"
)

plt.show()