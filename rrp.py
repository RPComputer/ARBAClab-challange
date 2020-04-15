import multiprocessing
from os import listdir
from copy import deepcopy
from time import time

'''
    This class represent a Can Remove policy rule. Stores the needed informations and have a method check that given two sets of roles,
    the first is the roles of a first user, the second is the roles of a different second user, the method returns true if the first user
    can remove the target role from the second user.
    The constructor parse the role.
'''
class RemoveTuple:
    def __init__(self, rule):
        if rule.startswith('<') and rule.endswith('>'):
            rule = rule[1:-1]
        rule = rule.split(',')
        self.ra = rule[0]
        self.rt = rule[1]
    
    def check(self, aroles, troles):
        if self.ra in aroles and self.rt in troles:
            return True
        return False

'''
    This class represent a Can Assign policy rule. Stores the needed informations and have a method check that given two sets of roles,
    the first is the roles of a first user, the second is the roles of a different second user, the method returns true if the first user
    can assign the target role to the second user.
    The constructor parse the role.
'''
class AssignTuple:
    def __init__(self, rule):
        if rule.startswith('<') and rule.endswith('>'):
            rule = rule[1:-1]
        rule = rule.split(',')
        self.ra = rule[0]
        self.rt = rule[2]
        self.Rp = []
        self.Rn = []
        self.flag = False
        if rule[1] == 'TRUE':
            self.flag = True
        else:
            rule = rule[1].split('&')
            for e in rule:
                if e[0] == '-':
                    self.Rn.append(e[1:])
                else:
                    self.Rp.append(e)
    
    def check(self, aroles, troles):
        if self.ra in aroles and self.rt not in troles:
            if self.flag:
                return True
            else:
                res = True
                for r in self.Rp:
                    if r not in troles:
                        res = False
                for r in self.Rn:
                    if r in troles:
                        res = False
                return res
    
    def __str__(self):
        return "("+self.ra+','+str(self.Rp)+','+str(self.Rn)+','+self.rt+')'

'''
    This class represents the Reaching Role Problem. It stores all the informations of the problem and owns three possible solution methods: standard solver (no optimization),
    forward solver (forward slicing), backwards solver (backwards slicing).
    Other functions are for auxiliari tasks and shouldn't be called by external objects, methods are private.
'''
class RRProblem:
    def __init__(self, pname, roles, users, UR, CA, CR, target):
        self.pname = pname
        self.roles = roles
        self.users = users
        self.UR = UR
        self.CA = CA
        self.CR = CR
        self.target = target
    
    '''
        This is the main solver method, it is an auxiliary function for the standard solver method and performs all the possible searches to try to assign the given 
        target role to a given target user, with a given assigning user. Returns true if possible and false otherwise.
        Method logic is explainend in the challange report.
    '''
    def __try_to_assign(self, ua, ut, UR, targetCA):
        for c in targetCA:
            nUR = deepcopy(UR)
            if c.check(nUR[ua], nUR[ut]):
                return True
            #Preparing the starting missing roles set
            missing_roles = set([x for x in c.Rp if x not in nUR[ut]])
            #to_remove_roles = set([x for x in c.Rn if x in nUR[ut]]) #uncomment to add the removing roles possibilities
            to_add_missing = []
            to_remove_missing = []
            did_something = True
            #Until nothing can be done, try to reach the assigning condition
            while did_something and missing_roles != []:
                did_something = False
                #Updating status of missing roles according to discovered needed roles
                missing_roles.update(to_add_missing)
                for x in to_remove_missing:
                    if x in missing_roles:
                        missing_roles.remove(x)
                to_add_missing = []
                to_remove_missing = []
                #Trying to assign to the target user every missing role for the target role
                for nr in missing_roles:
                    #Critical point: verify if any needed role can't be assigned because no one has the assigning role needed, if yes, try to add the assigning role to every possible user
                    can_assign = False
                    for u in self.users:
                        for ca in self.CA:
                            if ca.rt == nr and ca.ra in nUR[u]:
                                can_assign = True
                    #Not possible to assign the role case
                    if not can_assign:
                        assigned = False
                        newTargetRules = []
                        for ca in self.CA:
                            if ca.rt == nr:
                                for cc in self.CA:
                                    if cc.rt == ca.ra:
                                        newTargetRules.append(cc)
                                for u in self.users:
                                    for u1 in self.users:
                                        nnUR = deepcopy(nUR)
                                        if self.__try_to_assign(u, u1, nnUR, newTargetRules): #Critical point: after suitable preparation, recursive call for the assigning role, it's a sub RRP problem
                                            if u1 in nUR:
                                                assigned = True
                                                did_something = True
                                                nUR[u1].append(ca.ra)
                                            else:
                                                nUR[u1] = [ca.ra]
                                                did_something = True
                                                assigned = True
                        #If the sub RRP isn't successful, the search can be aborted
                        if not assigned:
                            return False
                    #Actual search to assign the missing roles after the suitable preparations
                    for ca in self.CA:
                        if ca.rt == nr:
                            for r in ca.Rp:
                                if r not in nUR[ut] and r not in missing_roles:
                                    to_add_missing.append(r)
                                    did_something = True
                            for u in self.users:
                                if ca.check(nUR[u], nUR[ut]):
                                    did_something = True
                                    if ut in nUR:
                                            nUR[ut].append(ca.rt)
                                    else:
                                        nUR[ut] = [ca.rt]
                                    to_remove_missing.append(ca.rt)
                '''
                #Uncomment this to add removing roles possibilities. WARNING: not fully implemented
                for cr in self.CR:
                    if cr.rt in to_remove_roles:
                        for u in self.users:
                            if cr.check(nUR[u], nUR[ut]):
                                if ut in nUR:
                                    nUR[ut].remove(cr.rt)
                                    to_remove_roles.remove(cr.rt)'''
            if c.check(nUR[ua], nUR[ut]):
                return True
        return False

    '''
        The standard solver method is the base solver of the problem, it calls the main solver private method after suitable preparation.
        Returns 0 or 1 as requested in the challange task.
    '''
    def standard_solver(self):
        targetCA = [c for c in self.CA if c.rt == self.target]
        UCA = []
        for u in self.users:
            for ta in targetCA:
                if ta.ra in self.UR[u]:
                    UCA.append(u)
        for ua in UCA:
            for ut in self.users:
                newUR = deepcopy(self.UR)
                if self.__try_to_assign(ua, ut, newUR, targetCA):
                    return 1
        return 0

    '''
        This methods implements the forward slicing optimization as given in the theory. After it forges a new equivalent RRP problem and calls the standard solver.
    '''
    def forward_slicing_solver(self):
        needed_roles = set()
        for r in self.UR.values():
            needed_roles.update(r)
        newCA = self.CA.copy()
        newCR = self.CR.copy()
        done = []
        added = True
        while added:
            added = False
            for ca in newCA:
                check_set = set()
                check_set.update(ca.Rp)
                check_set.add(ca.ra)
                if check_set.issubset(needed_roles):
                    needed_roles.add(ca.rt)
                    done.append(ca)
                    added = True
        to_remove = []
        for ca in newCA:
            if ca.rt not in needed_roles:
                to_remove.append(ca)
            else:
                for r in ca.Rp:
                    if r not in needed_roles:
                        to_remove.append(ca)
                        break
        for e in to_remove:
            newCA.remove(e)
        to_remove = []
        for cr in newCR:
            if cr.ra not in needed_roles or cr.rt not in needed_roles:
                to_remove.append(cr)
        for e in to_remove:
            newCR.remove(e)
        for ca in newCA:
            to_remove = []
            for r in ca.Rn:
                if r not in needed_roles:
                    to_remove.append(r)
            for t in to_remove:
                ca.Rn.remove(t)
        newUR = deepcopy(self.UR)
        for k in newUR:
            newUR[k] = [x for x in newUR[k] if x in needed_roles]
        new_problem = RRProblem(self.pname, list(needed_roles), self.users, newUR, newCA, newCR, self.target)
        return new_problem.standard_solver()

    '''
        This methods implements the backward slicing optimization as given in the theory. After it forges a new equivalent RRP problem and calls the standard solver.
    '''
    def backward_slicing_solver(self):
        newCA = self.CA.copy()
        newCR = self.CR.copy()
        needed_roles = set()
        needed_roles.add(self.target)
        added = True
        done = []
        while added:
            added = False
            for ca in newCA:
                if ca.rt in needed_roles and ca not in done:
                    needed_roles.update(ca.Rp)
                    needed_roles.update(ca.Rn)
                    needed_roles.add(ca.ra)
                    done.append(ca)
                    added = True
        to_remove = []
        for ca in newCA:
            if ca.rt not in needed_roles:
                to_remove.append(ca)
        for e in to_remove:
            newCA.remove(e)
        to_remove = []
        for cr in newCR:
            if cr.rt not in needed_roles:
                to_remove.append(cr)
        for e in to_remove:
            newCR.remove(e)
        newUR = deepcopy(self.UR)
        for k in newUR:
            newUR[k] = [x for x in newUR[k] if x in needed_roles]
        new_problem = RRProblem(self.pname, list(needed_roles), self.users, newUR, newCA, newCR, self.target)
        return new_problem.standard_solver()

'''
    This function is the parser function for any file formatted as given. It returns a RRP problem object representing the file problem.
'''
def problem_parser(filename):
    file = open(filename, "r")
    lines = file.readlines()
    file.close()
    lines = list(filter(lambda a: a != '\n', lines))
    if len(lines) != 6:
        raise Exception(filename + " not enought data, needed 6 lines of info, provided: " + str(len(lines)))
    roles = lines[0].split()[1:-1]
    users = lines[1].split()[1:-1]
    UR = dict()
    rules = lines[2].split()[1:-1]
    for rule in rules:
        if rule.startswith('<') and rule.endswith('>'):
            rule = rule[1:-1]
        rule = rule.split(',')
        if rule[0] in UR:
            UR[rule[0]].append(rule[1])
        else:
            UR[rule[0]] = [rule[1]]
    CA = []
    CR = []
    rules = lines[3].split()[1:-1]
    for r in rules:
        CR.append(RemoveTuple(r))
    rules = lines[4].split()[1:-1]
    for r in rules:
        CA.append(AssignTuple(r))
    target = lines[5].split()[1]
    return RRProblem(filename, roles, users, UR, CA, CR, target)

'''
    This function is a symplifying function, it just hides the actual solver of a problem from the main, useful in case of multiprocessing.
'''
def solver(problem):
    res = problem.backward_slicing_solver()
    print(problem.pname + " solved!\nResult: ", res, "\n\n")

if __name__ == "__main__":
    print("Solver working")
    problems = []
    path = input("Insert path to problems dir: ") #user have to insert the full path to a dir containing only .arbac files for parsing
    paths = listdir(path)
    print("Parsing started...")
    for p in paths:
        problems.append(problem_parser(path+'\\'+p))
    
    start_time = time()
    '''
    #Uncomment thtis to use the multiprocessing to increase the speed of the solution process, if there are more than one problems.
    print("Parsing completed\nStarting process pool...")
    pool = multiprocessing.Pool()
    pool.map(solver, problems) #each process works on a different problem
    pool.close()
    pool.join()
    print("Problems solved.")
    '''
    
    for p in problems:
        solver(p)
    print("Problems solved.")
    print("Time: ", time()-start_time)