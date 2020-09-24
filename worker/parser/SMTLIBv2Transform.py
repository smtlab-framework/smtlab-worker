# Generated from SMTLIBv2.g4 by ANTLR 4.8
import re
from antlr4 import *
#from SMTLIBv2Parser import *

if __name__ is not None and "." in __name__:
    from .SMTLIBv2Parser import SMTLIBv2Parser
else:
    from SMTLIBv2Parser import SMTLIBv2Parser

class SMTLIBv2Transform(ParseTreeVisitor):
    smtLibKeyWords = {"2.6" : ["re.comp","str.from_int", "str.to_int","str.in_re","str.to_re","re.none"],
                      "2.5" : ["re.complement","int.to.str", "str.to.int","str.in.re","str.to.re","re.nostr"]}

    smtLibEscapes = {"2.6" : ["\\u{"],
                     "2.5" : ["\\x"]}

    def visitChildren(self,ctx):
        waiting = [ctx]
        seen = []
        while len(waiting) > 0:
            child = waiting.pop()
            if isinstance(child, tree.Tree.TerminalNode):
                seen=[str(child)]+seen
            else:
                waiting+=list(child.getChildren())
        return seen[:-1] # remove <EOF>

    def postProcessStrings(self,sl):
        processed = []
        while len(sl) > 0:
            x = sl.pop(0)
            if x == "(":
                if len(sl) > 0 and sl[0] == ")":
                    processed+=[x]+[sl.pop(0)]
                else:
                    processedNew,sl = self.postProcessStrings(sl)
                    processed+=[processedNew]
            elif x == ")":
                return processed,sl
            else:
                processed+=[x]
        return processed,sl

    def getListInstance(self,ctx:SMTLIBv2Parser.StartContext):
        return self.postProcessStrings(self.visitChildren(ctx))[0]

    def flattenData(self,data):
        flattend = ""
        while len(data) > 0:
            s = data.pop(0)
            if type(s).__name__ == "list":
                flattend+=f"({self.flattenData(s)})"
            else:
                flattend+=f" {s} "
        return flattend

    # positive=True : remove declarations, positive=False : leave only declarations 
    def filterDeclarations(self,data,declarations,positive=True):
        stripData = []
        while len(data) > 0:
            s = data.pop(0)
            if type(s).__name__ == "list":
                if (positive and s[0] not in declarations) or (not positive and s[0] in declarations) :
                    stripData+=[self.filterDeclarations(s,declarations)]
            else:
                stripData+=[s]
        return stripData

    def modifyConstStrings(self,data,f):
        modData = []
        while len(data) > 0:
            s = data.pop(0)
            if type(s).__name__ == "list":
                modData+=[self.modifyConstStrings(s,f)]
            else:
                modData+=[s if not s.startswith('"') else f(s)]
        return modData

    def insertCommands(self,data,newData,index=1):
        return data[:index]+newData+data[index:]

    def dectetSMTLibVersion(self,data):
        smtLibVersion = None
        while len(data) > 0 and smtLibVersion == None:
            s = data.pop(0)
            if type(s).__name__ == "list":
                tmp_version = self.dectetSMTLibVersion(s)
                if tmp_version != None:
                    smtLibVersion = tmp_version
            else:
                # escape sequences
                if  s.startswith('"'):
                    for v in self.smtLibEscapes:
                        for e in self.smtLibEscapes[v]:
                            if e in s:
                                smtLibVersion=v
                                break;
                        if smtLibVersion != None:
                            break
                else:
                    for v in self.smtLibKeyWords:
                        if s in self.smtLibKeyWords[v]:
                            smtLibVersion=v
                            break

        return smtLibVersion


    ## smtlib 2.6 haxx
    def _translate_smt26_escape_to_smt25(self,text):
        return re.sub('u{(..)}', r'x\1', re.sub('u{(.)}', r'x0\1', text))
    def _translate_smt25_escape_to_smt26(self,text):
        return re.sub('\\\\x(..)', r'\\u{\1}', re.sub('\\\\'+'x0(.)', r'\\u{\1}', text)) 

del SMTLIBv2Parser