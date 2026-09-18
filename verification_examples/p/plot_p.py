import pandas as pd
import matplotlib
matplotlib.use("MacOSX")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pd.read_csv(
    os.path.join(path, "resultsp.csv"),
    header=None,
    names=["x", "u", "error"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

fig, axs = plt.subplots(
    2,
    1,
    figsize=(12, 7),
)


# Position
axs[0].plot(t, data["x"], label="P normal")

axs[0].set_ylabel("Position x")
axs[0].set_xlabel("Temps (s)")
axs[0].grid(True)
axs[0].legend()


# Commande
axs[1].plot(t, data["u"], color="red")

axs[1].set_ylabel("u")
axs[1].set_xlabel("Temps (s)")
axs[1].grid(True)


# Titre
fig.suptitle(
    "Response of a descrete P to a step",
    fontsize=16
)

# Espacement automatique
plt.tight_layout()

# Sauvegarde image
plt.savefig(
    os.path.join(path, "results_P.png"),
    dpi=300,
    bbox_inches="tight"
)

# Affichage interactif
plt.show()
