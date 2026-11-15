import pandas as pd
import matplotlib
# matplotlib.use("MacOSX")
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import os

path = os.path.dirname(os.path.abspath(__file__))

data = pd.read_csv(
    os.path.join(path, "resultsp.csv"),
    header=None,
    names=["x", "error", "eps", "kmin", "r"]
)

dt = 0.1
t = [i * dt for i in range(len(data))]

goal = data["r"][1]
x0 = data["x"][0]
error0 = data["error"][0]

kmin_t = data["kmin"][1] * dt

eps = data["eps"][1]


fig, axs = plt.subplots(
    2,
    1,
    figsize=(12, 7),
)


# Position
axs[0].plot(t, data["x"], label="system output")

axs[0].axhline(y=goal, color="green", linestyle="--", label="output goal (system upper bound)")
axs[0].axvline(x=kmin_t, color="orange", linestyle="--", label="kmin")
axs[0].axhline(y=(goal-eps), color="black", linestyle="--", label="system lower bound")


axs[0].annotate( f"kmin={data["kmin"][1]:.0f}", xy=(kmin_t, 0), xycoords=axs[0].get_xaxis_transform(),xytext=(0, -22), textcoords="offset points",
                ha="center", va="top", color="orange",annotation_clip=False,)

y_top_sys = goal
y_bot_sys = goal - eps
x_arrow = 0.8
axs[0].annotate("", xy=(x_arrow, y_top_sys), xytext=(x_arrow, y_bot_sys), xycoords=axs[0].get_yaxis_transform(), arrowprops=dict(arrowstyle="<->", color="red", lw=1.5),)
axs[0].text(x_arrow + 0.01, (y_top_sys + y_bot_sys) / 2, f"eps={eps * 100 / goal:.0f}%", transform=axs[0].get_yaxis_transform(), ha="left", va="center", color="red", )

axs[0].set_ylabel("meter")
axs[0].set_xlabel("Time (s)")
axs[0].grid(True)
axs[0].legend()


# Commande
axs[1].plot(t, data["error"], color="brown", label="error")

axs[1].axhline(y=0, color="green", linestyle="--", label="error goal (error lower bound)")
axs[1].axvline(x=kmin_t, color="orange", linestyle="--", label="kmin")
axs[1].axhline(y=(eps), color="black", linestyle="--", label="error upper bound")

y_top_error = eps
y_bot_error = 0
axs[1].annotate("", xy=(x_arrow, y_top_error), xytext=(x_arrow, y_bot_error), xycoords=axs[1].get_yaxis_transform(), arrowprops=dict(arrowstyle="<->", color="red", lw=1.5),)
axs[1].text(x_arrow + 0.01, (y_top_error + y_bot_error) / 2, f"eps={eps * 100 / goal:.0f}%", transform=axs[1].get_yaxis_transform(), ha="left", va="center", color="red", )

axs[1].set_ylabel("meter")
axs[1].set_xlabel("Time (s)")
axs[1].grid(True)
axs[1].legend()


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
