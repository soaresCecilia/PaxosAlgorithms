from os import listdir
from os.path import isfile, join

from os import close
import re
import os

import statistics

class MyStore:
    def __init__(self):
        self.tracker = { }

    def get(self, pAcc):
        return [e for e in self.tracker.values() if e.acc == pAcc]

class MyData:
    def __init__(self, pAcc, pStep, pScope, pValue, pBallot, pQuorum, pSolver, pStrategy, pRun, pTime):
        self.key = str(pStep) + '-' + str(pAcc) + '-' + pScope + '-' + pSolver + '-' + pStrategy
        self.acc = pAcc
        self.step = pStep
        self.value = pValue
        self.ballot = pBallot
        self.quorum = pQuorum
        self.scope = pScope
        self.solver = pSolver
        self.strategy = pStrategy
        self.run = pRun
        if pTime != 'Timeout' and pTime != 'Error' and pTime != '-':
            self.times = [float(pTime)]
            self.mean = str(round(float(pTime), 2))
        else:
            self.times = [pTime]
            self.mean = pTime

        self.std = str(0)

    def append(self, pTime):
        if pTime != 'Timeout' and self.mean != 'Timeout' and pTime != 'Error' and self.mean != 'Error' and pTime != '-' and self.mean != '-':
            self.times.append(float(pTime))
            self.mean = str(round(sum(self.times) / len(self.times), 2))
            self.std = str(round(statistics.stdev(self.times), 2))
        elif pTime != 'Timeout' and self.mean != 'Timeout' and pTime == 'Error' and self.mean == 'Error':
            self.times = ['Error']
            self.mean = 'Error'
        elif pTime != '-' and self.mean != '-' and pTime != 'Timeout' and self.mean != 'Timeout' and pTime != 'Error' and self.mean != 'Error':
            self.times = ['-']
            self.mean = '-'
        else:
            self.times = ['Timeout']
            self.mean = 'Timeout'

    def __repr__(self):
        return '{' + self.key + ', ' + str(self.acc) + ', ' + str(self.step) + ', ' + self.scope + ', ' + self.solver + ', ' + self.strategy + ', ' + str(self.mean) + '}'

def compute(store, lines, solver, strategy, run):
    for line in lines:
        if re.match("Label: ChosenValue", line):
            substringAcc = re.search(r'\d+ Acceptor', line).group()
            nAcc = int(re.search(r'\d+', substringAcc).group())

            
            search_time1 = re.search(r'Time: \d+', line)
            search_time2 = re.search(r'Time: Error', line)
            search_time3 = re.search(r'Time: -', line)
            if search_time1 is not None:   
                timesubstring = search_time1.group()
                msdigit = re.search(r'\d+', timesubstring).group()
                ms = str(int(msdigit)/1000)
            elif search_time2 is not None:
                ms = "Error"
            elif search_time3 is not None:
                ms = "-"
            else:
                ms = "Timeout"

            valueStr = re.search(r'\d+ Value', line).group()
            value = re.search(r'\d+', valueStr).group()
            BallotStr = re.search(r'\d+ Ballot', line).group()
            ballot = re.search(r'\d+', BallotStr).group()
            QuorumStr = re.search(r'\d+ Quorum', line).group()
            quorum = re.search(r'\d+', QuorumStr).group()

            StepsStr = re.search(r'Steps: \d+', line).group()
            steps = re.search(r'\d+', StepsStr).group()

            scope = 'V' + value + 'B' + ballot + 'Q' + quorum

            my_data = MyData(nAcc, int(steps), scope, int(value), int(ballot), int(quorum), solver, strategy, run, ms)

            if my_data.key not in store.tracker:
                store.tracker[my_data.key] = my_data
            else:
                my_saved_data = store.tracker[my_data.key]
                my_saved_data.append(ms)

def compute_files(my_path, run):
    store = MyStore()
    files = [f for f in listdir(my_path) if isfile(join(my_path, f)) and f.startswith(run) and f.endswith('.txt')]
    print(files)
    for file in files:
        file_name_info = file.replace(run + '-', '')
        solver, strategy, _ = file_name_info.split('-')
        lines = None
        with open(my_path + file) as f:
            re.search(r'\d+', f.readline()).group() # Discard information on min acceptors
            re.search(r'\d+', f.readline()).group() # Discard information on max acceptors
            lines = f.readlines()
        compute(store, lines, solver, strategy, run)

    return store


def generate_table(acc, data):
    print('\n\n\n\n\n------------' + str(acc) + '------------')
    ordered_data = sorted(data, key = lambda x: (x.acc, x.step, x.value, x.ballot, x.quorum, x.solver, x.strategy))

    scope = ''
    scope_number = 0
    scope_color = True

    row_color = True

    index = 0
    while index < len(ordered_data):
        if ordered_data[index].scope != scope:
            scope = ordered_data[index].scope
            step = ordered_data[index].step
            scope_number += 1
            if scope_number == 4: #linha onde se escreve o step
                if scope_color: #steps
                    print('\multirow{1}*{\cellcolor[HTML]{EFEFEF}' + str(step) + '} &')
                else:
                    print('\multirow{1}{*}{'  + str(step) + '} &')
                print('\multicolumn{1}{c}{' + scope + '} &')
            else:
                if scope_color: #a célula do step é cinzenta
                    if row_color: #o scope é cinzento
                        print('\multirow{1}*{\cellcolor[HTML]{EFEFEF}} &')
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}' + scope + '} &')
                    else:#o scope é branco
                        print('\multirow{1}*{\cellcolor[HTML]{EFEFEF}} &')
                        print('\multicolumn{1}{c}{' + scope + '} &')
                else: #a célula do step é branca
                    if row_color: #o scope cinzento
                        print('\multirow{1}*{} &')
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}' + scope + '} &')
                    else:#o scope é branco
                        print('\multirow{1}*{} &')
                        print('\multicolumn{1}{c}{' + scope + '} &')
            if scope_number == 8:
                scope_number = 0
                scope_color = not scope_color

        column_index_element = 0
        for inner_index in range(index, index + 10):
            mean = ordered_data[inner_index].mean
            std = ordered_data[inner_index].std
            version = ordered_data[inner_index].run
            acceptors = ordered_data[inner_index].acc
           # print(column_index_element)
           # print(version)
           # print(acceptors)
           # print(scope)
            if row_color:
                #print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{' + mean + '/' + std + '}} ', end = '')
                print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{' + mean + '}} ', end = '')
            else:
                #print('\multicolumn{1}{c}{' + mean + '/' + std  +  '} ', end = ''),
                print('\multicolumn{1}{c}{' + mean +  '} ', end = ''),
            if column_index_element != 9:
                print('&')
                column_index_element += 1
            elif column_index_element == 9 and (version == 'paxos-no-message' or version == 'paxos-dynamic-message'):
                print('&')
                if 'Q3' in scope and row_color:
                    if acceptors == 3:
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{16}}')
                    elif acceptors == 4:
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{44}}')
                elif 'Q2' in scope and row_color:
                    if acceptors == 3:
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{5}}')
                    elif acceptors == 4:
                        print('\multicolumn{1}{c}{\cellcolor[HTML]{EFEFEF}\\textbf{8}}')
                elif 'Q3' in scope and not row_color:
                    if acceptors == 3:
                        print('\multicolumn{1}{c}{16}')
                    elif acceptors == 4:
                        print('\multicolumn{1}{c}{44}')
                elif 'Q2' in scope and not row_color:
                    if acceptors == 3:
                        print('\multicolumn{1}{c}{5}')
                    elif acceptors == 4:
                        print('\multicolumn{1}{c}{8}')  
                if 'V3B3Q3' in scope:                
                    print('\\\\' + '\hline')
                else:
                    print('\\\\')
            else:
                print('\\\\')
        row_color = not row_color
        index += 10


# scope-vertical-paxosI-no-message
# scope-vertical-paxosII-no-message
# scope-paxos-no-message
# scope-paxos-dynamic-message
# scope-paxos-static-message
directory = os.getcwd(); #root of project

#my_path = directory + '/Plots/results/paxos/'
my_path = directory + '/Plots/results/vertical/'

run = 'scope-vertical-paxosII-no-message'

store = compute_files(my_path, run)

threeAcceptors = store.get(3)
generate_table(3, threeAcceptors)

#fourAcceptors = store.get(4)
#generate_table(4, fourAcceptors)
