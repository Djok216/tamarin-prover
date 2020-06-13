#include <iostream>
#include <map>
#include "fastterm.h"
#include "fastqueryacunify.h"
using namespace std;

constexpr int kSortPub = 7;
constexpr int kSortFresh = 8;
constexpr int kSortMsg = 9;
constexpr int kSortNode = 10;

map<int, FastSort> mapSorts;

void initTamarinSorts() {
  mapSorts[kSortPub] = newSort("LSortPub");
  mapSorts[kSortFresh] = newSort("LSortFresh");
  mapSorts[kSortMsg] = newSort("LSortMsg");
  mapSorts[kSortNode] = newSort("LSortNode");
  newSubSort(mapSorts[kSortFresh], mapSorts[kSortMsg]);
  newSubSort(mapSorts[kSortPub], mapSorts[kSortMsg]);
  assert(isSubSortTransitive(mapSorts[kSortFresh], mapSorts[kSortMsg]));
}

// Problema din haskell: Xor(~r0.6,r1.7,h(k0.8)) =? Xor(~r1.1,h(k0.2))
// daca variabila incepe cu "~r" are sortul fresh, daca incepe cu "r" sau "k" atunci sortul e MSG.
// 
// In C++ ajunge ceva de felul acesta (sorturile sunt la fel ca in haskell):
// solve AC-unify: f(y1, x5, g(x4) =? f(y2, g(x2))
// Unifications: 4
// {y2 |-> f(_13, _14, g(x4)), y1 |-> _13, x5 |-> f(_14, g(x2))}
// {y2 |-> f(_13, g(x4)), y1 |-> _13, x5 |-> g(x2)}
// {y2 |-> f(_13, _14, g(x4)), y1 |-> f(_13, g(x2)), x5 |-> _14}
// {y2 |-> f(_14, g(x4)), y1 |-> g(x2), x5 |-> _14}
void exemplul1() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastVar x4 = newVar("x4", mapSorts[kSortMsg]);
  FastVar x5 = newVar("x5", mapSorts[kSortMsg]);
  FastVar y1 = newVar("y1", mapSorts[kSortFresh]);
  FastVar y2 = newVar("y2", mapSorts[kSortFresh]);
  FastSort sorts[6] = {mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);

  FastTerm args[2] = {x4, x2};
  FastTerm g4 = newFuncTerm(g, args);
  FastTerm g2 = newFuncTerm(g, args + 1);
  args[0] = y1; args[1] = x5;
  FastTerm t1 = newFuncTerm(f, args);
  args[0] = t1; args[1] = g4;
  t1 = newFuncTerm(f, args);
  args[0] = y2; args[1] = g2;
  FastTerm t2 = newFuncTerm(f, args);

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  cout << "Number of unifiers: " << ans.size() << '\n';
  for (auto& subst : ans) cout << toString(subst) << '\n';
}

void exemplul2() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastVar x4 = newVar("x4", mapSorts[kSortMsg]);
  FastVar x5 = newVar("x5", mapSorts[kSortMsg]);
  FastVar y1 = newVar("y1", mapSorts[kSortFresh]);
  FastVar y2 = newVar("y2", mapSorts[kSortFresh]);
  FastSort sorts[6] = {mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);

  FastTerm args[2] = {y1, x2};
  FastTerm t1 = newFuncTerm(f, args);
  FastTerm t2 = y2;

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  cout << "Number of unifiers: " << ans.size() << '\n';
  for (auto& subst : ans) cout << toString(subst) << '\n';
}

//tamXxor(tamXxor(Y1, X1), X2) =? tamXxor(Y2, C) 
void exemplul3() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastVar x4 = newVar("x4", mapSorts[kSortMsg]);
  FastVar x5 = newVar("x5", mapSorts[kSortMsg]);
  FastVar y1 = newVar("y1", mapSorts[kSortFresh]);
  FastVar y2 = newVar("y2", mapSorts[kSortFresh]);
  FastSort sorts[6] = {mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);
  FastFunc c1 = newConst("c1", mapSorts[kSortMsg]);
  FastFunc c2 = newConst("c2", mapSorts[kSortMsg]);
  FastTerm cTerm = newFuncTerm(c1, nullptr);

  FastTerm args[2] = {x4, x2};
  FastTerm g4 = newFuncTerm(g, args);
  FastTerm g2 = newFuncTerm(g, args + 1);
  args[0] = y1; args[1] = x5;
  FastTerm t1 = newFuncTerm(f, args);
  args[0] = t1; args[1] = g4;
  t1 = newFuncTerm(f, args);
  args[0] = y2; args[1] = g2;
  FastTerm t2 = newFuncTerm(f, args);

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  cout << "Number of unifiers: " << ans.size() << '\n';
  for (auto& subst : ans) cout << toString(subst) << '\n';
}

// (HsACf0#5(LSortMsg) HsVar5#5(LSortFresh) (HsNoEqf1#5(LSortMsg) HsVar4#5(LSortMsg))) (HsACf0#5(LSortMsg) HsVar3#5(LSortFresh) (HsNoEqf1#5(LSortMsg) HsVar2#5(LSortMsg)))
// [Equal {eqLHS = Xor(~r0.6,h(k0.7)), eqRHS = Xor(~r1.1,h(k0.2))}]
void exemplul4() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastVar x4 = newVar("x4", mapSorts[kSortMsg]);
  FastVar x5 = newVar("x5", mapSorts[kSortMsg]);
  FastVar y1 = newVar("y1", mapSorts[kSortFresh]);
  FastVar y2 = newVar("y2", mapSorts[kSortFresh]);
  FastSort sorts[6] = {mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);

  FastTerm args[2] = {x4, x2};
  FastTerm g4 = newFuncTerm(g, args);
  FastTerm g2 = newFuncTerm(g, args + 1);
  args[0] = y1; args[1] = g4;
  FastTerm t1 = newFuncTerm(f, args);
  args[0] = y2; args[1] = g2;
  FastTerm t2 = newFuncTerm(f, args);

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  cout << "Number of unifiers: " << ans.size() << '\n';
  for (auto& subst : ans) cout << toString(subst) << '\n';
}

void exemplul5() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastSort sorts[6] = {mapSorts[kSortFresh], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);
  FastFunc c2 = newConst("c2", mapSorts[kSortFresh]);
  FastFunc c3 = newConst("c3", mapSorts[kSortFresh]);
  FastFunc c4 = newConst("c4", mapSorts[kSortFresh]);
  FastFunc c5 = newConst("c5", mapSorts[kSortFresh]);
  FastTerm c2t = newFuncTerm(c2, nullptr);
  FastTerm c3t = newFuncTerm(c3, nullptr);
  FastTerm c4t = newFuncTerm(c4, nullptr);
  FastTerm c5t = newFuncTerm(c5, nullptr);

  FastTerm args[2] = {c2t, c3t};
  FastTerm gc2 = newFuncTerm(g, args);

  FastTerm aux1 = newFuncTerm(f, args);
  args[0] = c4t; args[1] = x2;
  FastTerm aux2 = newFuncTerm(f, args);
  args[0] = aux1; args[1] = aux2;
  FastTerm aux3 = newFuncTerm(f, args);
  args[0] = aux3; args[1] = gc2;
  FastTerm t1 = newFuncTerm(f, args);

  args[0] = c2t; args[1] = c2t;
  aux1 = newFuncTerm(f, args);
  args[0] = c3t; args[1] = c4t;
  aux2 = newFuncTerm(f, args);
  args[0] = aux1; args[1] = aux2;
  aux3 = newFuncTerm(f, args);
  args[0] = c5t; args[1] = gc2;
  FastTerm aux4 = newFuncTerm(f, args);
  args[0] = aux3; args[1] = aux4;
  FastTerm t2 = newFuncTerm(f, args);

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  cout << eq_term(t1, t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  cout << "Number of unifiers: " << ans.size() << '\n';
  for (auto& subst : ans) cout << toString(subst) << '\n';
}


int main() {
  //exemplul1();
  //exemplul2();
  //exemplul3();
  //exemplul4();
  exemplul5();
  return 0;
}