import Core
namespace PEqualNP.Outside.Comparator9929
def group0 : List (Nat × List Sig) := [(1,rawInputs), (2,rawInputs), (3,rawInputs)]
def group1 : List (Nat × List Sig) := [(4,rawInputs), (5,rawInputs), (6,rawInputs)]
def allRoots := group0 ++ group1
def reject (p : Nat × List Sig) := !(search 11 p.1 p.2)
end PEqualNP.Outside.Comparator9929
