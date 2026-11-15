import pandas as pi
import matplotlib
matplotlib.use("MacOSX")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pi.read_csv(
    os.path.join(path, "resultspi.csv"),
    header=None,
    names=["x", "u", "error", "integral"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

fig, axs = plt.subplots(
    2,
    1,
    figsize=(12, 7),
)


# Position
axs[0].plot(t, data["x"], label="PI normal")

axs[0].set_ylabel("Position x")
axs[0].set_xlabel("Temps (s)")
axs[0].grid(True)
axs[0].legend()


# Commande
axs[1].plot(t, data["integral"], color="red")

axs[1].set_ylabel("integral")
axs[1].set_xlabel("Temps (s)")
axs[1].grid(True)


# Titre
fig.suptitle(
    "Response of a descrete pi to a step on a simple sys",
    fontsize=16
)

# Espacement automatique
plt.tight_layout()

# Sauvegarde image
plt.savefig(
    os.path.join(path, "results_pi.png"),
    dpi=300,
    bbox_inches="tight"
)

# Affichage interactif
plt.show()
