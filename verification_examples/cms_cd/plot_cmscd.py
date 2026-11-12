import pandas as pd
import matplotlib
matplotlib.use("MacOSX")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pd.read_csv(
    os.path.join(path, "resultscd.csv"),
    header=None,
    names=["x", "v", "u", "x_esin", "noise", "x_estat", "x_e"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

fig, axs = plt.subplots(
    3,
    1,
    figsize=(12, 7),
)


# Position
axs[0].plot(t, data["x"], label="PID normal")
axs[0].plot(t, data["x_esin"], label="PID + noise")
axs[0].plot(t, data["x_estat"], label="PID + offset")
axs[0].plot(t, data["x_e"], label="PID + noise & offset")

axs[0].set_ylabel("Position x")
axs[0].set_xlabel("Temps (s)")
axs[0].grid(True)
axs[0].legend()


# Vitesse
axs[1].plot(t, data["v"], color="green")

axs[1].set_ylabel("Speed v normal PID")
axs[1].set_xlabel("Temps (s)")
axs[1].grid(True)


# Commande
axs[2].plot(t, data["u"], color="red")

axs[2].set_ylabel("Control u normal PID")
axs[2].set_xlabel("Temps (s)")
axs[2].grid(True)


# Titre
fig.suptitle(
    "Controlled mass spring system, continuous system & descrete PID",
    fontsize=16
)

# Espacement automatique
plt.tight_layout()

# Sauvegarde image
plt.savefig(
    os.path.join(path, "resultscd_PID.png"),
    dpi=300,
    bbox_inches="tight"
)

# Affichage interactif
plt.show()
