import pandas as pd
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pd.read_csv(
    os.path.join(path, "resultspd_param.csv"),
    header=None,
    names=["x", "u", "error", "derivative", "a", "b"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

fig, axs = plt.subplots(
    2,
    1,
    figsize=(12, 7),
)


# Position
axs[0].plot(t, data["x"])

axs[0].set_ylabel("System output x")
axs[0].set_xlabel("Time (s)")
axs[0].grid(True)


# Commande
axs[1].plot(t, data["u"], color="red")

axs[1].set_ylabel("Controller output u")
axs[1].set_xlabel("Time (s)")
axs[1].grid(True)





# Titre
fig.suptitle(
    "Response of a descrete parametric PD on a simple sys to a step",
    fontsize=16
)

# Espacement automatique
plt.tight_layout()

# Sauvegarde image
plt.savefig(
    os.path.join(path, "results_pd_param.png"),
    dpi=300,
    bbox_inches="tight"
)

# Affichage interactif
plt.show()
