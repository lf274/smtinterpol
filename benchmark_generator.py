import sys
from random import random, randrange


class BenchmarkGenerator:
    def __init__(self, numVariables, largestFormula, probability, filename="test123.smt2") -> None:
        self.numVariables = numVariables
        self.formulae = []
        self.dictOfVariables = {}
        for i in range(self.numVariables):
            self.dictOfVariables[i] = 0
        self.largestFormula = largestFormula
        self.probability = probability
        self.fileName = filename

    def createFormula(self) -> None:
        formula = []
        # random zahl zw 2 und largestFormula: Anzal der beteiligten Variablen
        formula_length = randrange(3, largestFormula + 1)
        for i in range(self.numVariables):
            # jede variable wird mit Warscheinlichkeit probability in der Formel beteiligt sein
            if random() < self.probability:
                formula.append(i)
                self.dictOfVariables[i] += 1
            if len(formula) >= formula_length:
                break
        self.formulae.append(formula)

    def checkEven(self):
        # alle var, die nicht gerade oft vorkommen, werden nochmal in eine formel geschmissen
        formula = []
        for key, value in self.dictOfVariables.items():
            if value % 2 != 0:
                formula.append(key)
        if len(formula) == 0:
            self.createFormula
        if len(formula) > 1:
            self.formulae.append(formula)
        else:
            atom = formula[0]
            for element in self.formulae:
                if len(element) > 3 and atom not in element:
                    element.append(atom)
                    self.partitionFormula(element)

    def partitionFormula(self, formula):
        middle_index = len(formula) // 2
        partial_formula_1 = formula[:middle_index]
        partial_formula_2 = formula[middle_index:]
        self.formulae.remove(formula)
        self.formulae.append(partial_formula_1)
        self.formulae.append(partial_formula_2)

    def formulaToString(self, formula) -> str:
        formulaString = "(assert (xor"
        for variable in formula:
            formulaString += " |{}|".format(variable)
        formulaString += "))\n"
        return formulaString

    def generateBenchmarks(self) -> None:
        for i in range(self.numVariables - 1):
            self.createFormula()
        self.checkEven()
        with open(self.fileName, 'w') as f:
            f.write("(set-option :produce-models true)\n(set-option :timeout 3000000)\n(set-logic CORE)\n")
            for i in range(self.numVariables):
                f.write("(declare-fun |{}| () Bool)\n".format(i))
            for formula in self.formulae:
                formulaString = self.formulaToString(formula)
                f.write(formulaString)
            f.write("(check-sat)")


if __name__ == "__main__":
    if len(sys.argv) == 5:
        numVariables = int(sys.argv[1])
        largestFormula = int(sys.argv[2])
        probability = float(sys.argv[3])
        numOfBenchmarks = int(sys.argv[4])
        for i in range(numOfBenchmarks):
            filename = "XorTest{}_{}".format(numVariables, i)
            benchmarkGenerator = BenchmarkGenerator(numVariables, largestFormula, probability, filename)
            benchmarkGenerator.generateBenchmarks()
    elif len(sys.argv) == 1:
        print("super mode\n")
        for i in range(1, 6):
            numVariables = i * 10
            largestFormula = numVariables
            for j in range(4):
                filename = "bm_{}_{}".format(numVariables, j)
                benchmarkGenerator = BenchmarkGenerator(numVariables, largestFormula, 0.5, filename)
                benchmarkGenerator.generateBenchmarks()
            
    else:
        print("pls use as intended:\n")
        print("python3 benchmark_generator.py numVariables largestFormula probability numOfBenchmarks\n")