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
}

// Problema din haskell: Xor(~r0.6,r1.7,h(k0.8)) =? Xor(~r1.1,h(k0.2))
// daca variabila incepe cu "~r" are sortul fresh, daca incepe cu "r" sau "k" atunci sortul e MSG.
// 
// In C++ ajunge ceva de felul acesta (sorturile sunt la fel ca in haskell):
// solve AC-unify: f(x6, x5, g(x4) =? f(x3, g(x2))
// Unifications: 4
// {x3 |-> f(_13, _14, g(x4)), x6 |-> _13, x5 |-> f(_14, g(x2))}
// {x3 |-> f(_13, g(x4)), x6 |-> _13, x5 |-> g(x2)}
// {x3 |-> f(_13, _14, g(x4)), x6 |-> f(_13, g(x2)), x5 |-> _14}
// {x3 |-> f(_14, g(x4)), x6 |-> g(x2), x5 |-> _14}
void exemplul1() {
  initTamarinSorts();
  FastVar x2 = newVar("x2", mapSorts[kSortMsg]);
  FastVar x4 = newVar("x4", mapSorts[kSortMsg]);
  FastVar x5 = newVar("x5", mapSorts[kSortMsg]);
  FastVar x6 = newVar("x6", mapSorts[kSortFresh]);
  FastVar x3 = newVar("x3", mapSorts[kSortFresh]);
  FastSort sorts[6] = {mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg], 
                  mapSorts[kSortMsg], mapSorts[kSortMsg]};
  FastFunc g = newFunc("g", mapSorts[kSortMsg], 1, sorts);
  FastFunc f = newACFunc("f", mapSorts[kSortMsg]);

  FastTerm args[2] = {x4, x2};
  FastTerm g4 = newFuncTerm(g, args);
  FastTerm g2 = newFuncTerm(g, args + 1);
  args[0] = x6; args[1] = x5;
  FastTerm t1 = newFuncTerm(f, args);
  args[0] = t1; args[1] = g4;
  t1 = newFuncTerm(f, args);
  args[0] = x3; args[1] = g2;
  FastTerm t2 = newFuncTerm(f, args);

  cout << "AC-Unify: " << toString(t1) << ' ' << toString(t2) << '\n';
  FastQueryACUnify solver(t1, t2);
  auto ans = solver.solve();
  for (auto& subst : ans) cout << toString(subst) << '\n';
}

int main() {
  exemplul1();
  return 0;
}