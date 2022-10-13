import numpy as np
import matplotlib.pyplot as plt
 
  

# set width of bar
barWidth = 0.23
fig = plt.subplots(figsize =(12, 8))
plt.rcParams["figure.autolayout"] = True
 
# set height of bar em segundos
nuXmvBatch = [161.267, 510.589, 477.512, 4181.169]
nuXmvHib = [171.324, 632.19, 452.352, 4546.45]
nuXmvPar = [251.915, 838.601, 446.154, 4189.866]
tla = [9.33, 115, 11.33, 160.33]

#minutos
#nuXmvBatch = [4.04, 95.21]
#nuXmvPar = [9.41, 0]
#nuXmvHib = [9.83, 0]
#tla = [0.58, 11.58]

# Set position of bar on X axis
br1 = np.arange(len(nuXmvBatch))
br2 = [x + barWidth for x in br1]
br3 = [x + barWidth for x in br2]
br4 = [x + barWidth for x in br3]

#bar colors
a = '#bab536'
b = '#de8135'
c = '#30a65f'
d = '#166b9c'
 
# Make the plot
bar1 = plt.bar(br1, nuXmvBatch, color = a, width = barWidth,
        edgecolor ='grey', label ='ElectrodX(Batch)')
bar2 = plt.bar(br2, nuXmvHib, color =c , width = barWidth,
        edgecolor ='grey', label ='ElectrodX(Híbrido)')
bar3 = plt.bar(br3, nuXmvPar, color =b , width = barWidth,
        edgecolor ='grey', label ='ElectrodX(Paralelo)')
bar4 = plt.bar(br4, tla, color = d, width = barWidth,
        edgecolor ='grey', label ='TLA+')

 
# Adding Xticks
plt.xlabel("Escopo de Execução")
plt.ylabel("Tempo de Execução em (segundos)")
#plt.title("Resultados da verificação automática ilimatada do Alloy e do TLA+")
plt.xticks([(r + barWidth + 0.05) for r in range(len(nuXmvBatch))],
        ['A3V3B3Q2', 'A3V3B4Q2', 'A3V4B3Q2', 'A4V3B3Q3'])
 
 
 # Add counts above the two bar graphs
for rect in bar1 + bar2 +bar3 + bar4:
    height = rect.get_height()
    plt.text(rect.get_x() + rect.get_width() / 2, height, f'{height:.2f}', 
             ha='center', va='baseline', c = 'grey')

plt.legend()
plt.tight_layout()
plt.show()
 
