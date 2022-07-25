#No import statements.

MAX_CONSTANTS = 10



# Parse a formula, consult parseOutputs for return values.
def parse(fmla):
    length = len(fmla)
    if length == 1:
        if checkIfProp(fmla) :
            return 6
    if length == 6:
        if checkIfPred(fmla):
            return 1
    if fmla[0] == '-' and length > 1:
        if parse(fmla[1:length]) in range (1,6):
            return 2
        elif parse(fmla[1:length]) in range(6,9):
            return 7
    if fmla[0] == 'E' and isVar(fmla[1]):
        if parse(fmla[2:length])!= 0:
            return 4
    if fmla[0] == 'A' and isVar(fmla[1]):
        if parse(fmla[2:length])!=0:
            return 3
    if fmla[0] == '(' and fmla[length-1] == ')' and length >= 5:
        return checkBConnect(fmla)   
    return 0

def checkBConnect(fmla):
    connective = con(fmla)
    if connective == None:
        return False
    left = lhs(fmla)
    right = rhs(fmla)
    if parse(left) in range(1,6) and parse(right) in range(1,6):
        return 5
    elif parse(left) in range(6,9) and parse(right) in range(6,9):
        return 8
    else:
        return 0


def checkBrackets(fmla):
    counter = 0
    for c in fmla:
        if c == '(':
            counter= counter + 1
        if c == ')':
            counter = counter - 1
    if counter == 0:
        return True
    else:
        return False

def isVar(char):
    constants = ['a','b','c','d','e','f','g','h','i','j']
    if char == 'x' or char == 'y' or char == 'z' or char =='w' or char in constants:
        return True
    else:
        return False

def checkIfPred(fmla):
    if fmla[0] == 'P' or fmla[0] == 'Q' or fmla[0] == 'R' or fmla[0] == 'S':
        if checkBrackets(fmla):
            if fmla[3] == ',' and (isVar(fmla[2]) and isVar(fmla[4])):
                return True
    return False


def checkIfProp(fmla):
    if fmla == 'p' or fmla == 'q'  or fmla == 'r' or fmla == 's':
        return True
    else:
        return False
# Return the LHS of a binary connective formula
def lhs(fmla):
    connective = con(fmla)
    loc = getConLoc(fmla,connective)
    return fmla[1:loc]

def getConLoc(fmla,connective):
    count = 1
    bracCount = 0
    for c in fmla[1:len(fmla)-1]:
        if c == '(':
            bracCount = bracCount + 1
        if c == ')':
            bracCount = bracCount - 1
        if c == connective and bracCount == 0:
            return count
        count = count + 1
    

# Return the connective symbol of a binary connective formula
def con(fmla):
    connective = None
    bracCount = 0 
    for c in fmla[1:len(fmla)-1]:
        if c == '(':
            bracCount = bracCount + 1
        if c == ')':
            bracCount = bracCount - 1
        if (c == '>' or c == 'v' or c == '^') and bracCount == 0:
            connective = c
            break
    return connective

# Return the RHS symbol of a binary connective formula
def rhs(fmla):
    connective = con(fmla)
    loc = getConLoc(fmla,connective)
    return fmla[loc+1:len(fmla)-1]


# You may choose to represent a theory as a set or a list
def theory(fmla):#initialise a theory with a single formula in it
    return [fmla]

#check for satisfiability
def sat(tableau):
#output 0 if not satisfiable, output 1 if satisfiable, output 2 if number of constants exceeds MAX_CONSTANTS
    new_consts = 0
    gam_dict = {}
    while tableau != []:
        th = tableau.pop(0)
        if exp(th) and (not c(th)):
            return 1
        else:
            fmla = None
            for f in th:
                if not(isLiteral(f)):
                    fmla = f
                    break
            if isAlpha(fmla):
                th.remove(fmla)
                toAdd = applyAlpha(fmla)
                for f in toAdd:
                    th.append(f)
                if not(c(th)) and (th not in tableau):
                    tableau.append(th)
            if isBeta(fmla):
                th1 = th.copy()
                th2 = th.copy()
                th1.remove(fmla)
                th2.remove(fmla)
                toAdd = applyBeta(fmla)
                th1.append(toAdd[0])
                th2.append(toAdd[1])
                if not(c(th1)) and (th1 not in tableau):
                    tableau.append(th1)
                if not(c(th2)) and (th2 not in tableau):
                    tableau.append(th2)
            if isDelta(fmla):
                if new_consts == MAX_CONSTANTS:
                    return 2
                else:
                    th.remove(fmla)
                    th.append(applyDelta(fmla,new_consts))
                    if not(c(th)) and (th not in tableau):
                        tableau.append(th)
                    new_consts = new_consts + 1
            if isGamma(fmla):
                if others(th,fmla):
                    th.remove(fmla)
                    th.append(fmla)
                else:
                    constants = ['a','b','c','d','e','f','g','h','i','j']
                    if fmla not in gam_dict:
                        gam_dict[fmla] = 0
                    if gam_dict[fmla] == new_consts:
                        th.remove(fmla)
                    else:
                        th.append(applyGamma(fmla,constants[gam_dict[fmla]]))
                        gam_dict[fmla] = gam_dict[fmla] + 1

                if not(c(th)) and (th not in tableau):
                    tableau.append(th)

    return 0

def others(th,fmla):
    newTh = th.copy()
    newTh.remove(fmla)
    for f in newTh:
        if parse(f) == 2 and parse(f[1:len(f)]) == 3:
            return True
        elif parse(f) == 4 or parse(f) == 5 or parse(f) == 8:
            return True
        elif parse(f) == 7 and not(len(f)==2):
            return True
    return False


def isGamma(fmla):
    if parse(fmla) == 3:
        return 1
    elif parse(fmla) == 2 and parse(fmla[1:len(fmla)]) == 4:
        return 2
    else:
        return 0

def applyGamma(fmla,const):
    if parse(fmla) == 3:
        var = fmla[1]
        return fmla[2:len(fmla)].replace(var,const)
    else:
        var = fmla[2]
        return ("-" + fmla[3:len(fmla)].replace(var,const))



def isDelta(fmla):
    if parse(fmla) == 4:
        return 1
    elif parse(fmla) == 2 and parse(fmla[1:len(fmla)]) == 3:
        return 2
    else:
        return 0

def applyDelta(fmla,const_num):
    constants = ['a','b','c','d','e','f','g','h','i','j']
    const = constants[const_num]
    if parse(fmla) == 4:
        var = fmla[1]
        return (fmla[2:len(fmla)].replace(var,const))
    else:
        var = fmla[2]
        return ("-" + fmla[3:len(fmla)].replace(var,const))


def isBeta(fmla):
    if fmla[0] == '-' and (parse(fmla[1:len(fmla)])== 5 or parse(fmla[1:len(fmla)])== 8):
        if con(fmla[1:len(fmla)]) == '^':
            return 1 
    elif parse(fmla)== 5 or parse(fmla)== 8:
        if con(fmla) == '>':
            return 2
        if con(fmla) == 'v':
            return 3
    else:
        return 0

def isAlpha(fmla):
    if fmla[0] == '-' and fmla[1] == '-':
        return 1
    elif fmla[0] == '-' and (parse(fmla[1:len(fmla)])== 5 or parse(fmla[1:len(fmla)])== 8):
        if con(fmla[1:len(fmla)]) == 'v':
            return 2
        if con(fmla[1:len(fmla)]) == '>':
            return 4
    elif (parse(fmla) == 5 or parse(fmla) == 8) and con(fmla) == '^':
        return 3
    else:
        return 0

def applyAlpha(fmla):
    if isAlpha(fmla) == 1:
        return [fmla[2:len(fmla)]]
    elif isAlpha(fmla) == 2:
        return ["-" + lhs(fmla[1:len(fmla)]), "-" + rhs(fmla[1:len(fmla)])]
    elif isAlpha(fmla) == 4:
        return[lhs(fmla[1:len(fmla)]),"-" + rhs(fmla[1:len(fmla)]) ]
    else:
        return [lhs(fmla),rhs(fmla)]

def applyBeta(fmla):
    if isBeta(fmla) == 1:
        return["-" + lhs(fmla[1:len(fmla)]), "-" + rhs(fmla[1:len(fmla)])]
    elif isBeta(fmla) == 2:
        return["-" + lhs(fmla), rhs(fmla)]
    else:
        return[lhs(fmla), rhs(fmla)]

def exp(th):
    constants = ['a','b','c','d','e','f','g','h','i','j']
    for f in th:
        ftype = parse(f)
        if ftype == 2:
            if len(f) != 7:
                return False
        elif ftype == 3 or ftype == 4 or ftype == 5 or ftype == 8:
            return False
        elif ftype == 7:
            if len(f) != 2:
                return False
    return True

def c(th):
    for f in th:
        notf = "-"+f
        for g in th:
            if g == notf:
                return True
    return False

def isLiteral(fmla):
    if parse(fmla) == 1 or parse(fmla) == 6:
        return True
    elif parse(fmla) == 2 or parse(fmla) == 7:
        if parse(fmla[1:len(fmla)]) == 1 or parse(fmla[1:len(fmla)]) == 6:
            return True
    else:
        return False

#DO NOT MODIFY THE CODE BELOW
f = open('input.txt')

parseOutputs = ['not a formula',
                'an atom',
                'a negation of a first order logic formula',
                'a universally quantified formula',
                'an existentially quantified formula',
                'a binary connective first order formula',
                'a proposition',
                'a negation of a propositional formula',
                'a binary connective propositional formula']

satOutput = ['is not satisfiable', 'is satisfiable', 'may or may not be satisfiable']



firstline = f.readline()

PARSE = False
if 'PARSE' in firstline:
    PARSE = True

SAT = False
if 'SAT' in firstline:
    SAT = True

for line in f:
    if line[-1] == '\n':
        line = line[:-1]
    parsed = parse(line)

    if PARSE:
        output = "%s is %s." % (line, parseOutputs[parsed])
        if parsed in [5,8]:
            output += " Its left hand side is %s, its connective is %s, and its right hand side is %s." % (lhs(line), con(line) ,rhs(line))
        print(output)

    if SAT:
        if parsed:
            tableau = [theory(line)]
            print('%s %s.' % (line, satOutput[sat(tableau)]))
        else:
            print('%s is not a formula.' % line)
