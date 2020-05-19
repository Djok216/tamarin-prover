#include "CppApi.h"
#include <iostream>
#include <stack>
#include <vector>
#include <tuple>
#include <cassert>
#include "fastterm.h"
using namespace std;

constexpr int kTypeNoType = -1;
constexpr int kTypeConst = 0;
constexpr int kTypeVar = 1;
constexpr int kTypeNoEq = 2;
constexpr int kTypeAC = 3;
constexpr int kTypeC = 4;
constexpr int kTypeList = 5;

constexpr const char* kNameConvert[] = {"const", "var", "NoEqf", "ACf", "Cf", "Listf"};

FastTerm combineTerms(const string& name, int type, vector<FastTerm>& terms, vector<FastSort>& sorts) {
  if (type != kTypeAC) {
    FastFunc f = newFunc(name.c_str(), fastStateSort(), terms.size(), &sorts[0]);
    return newFuncTerm(f, &terms[0]);
  }
  FastFunc f = newACFunc(name.c_str(), fastStateSort());
  for (int sz = 2; sz <= terms.size(); sz *= 2)
    for (int i = 0; i + sz / 2 < terms.size(); i += sz) {
      FastTerm args[2] = {terms[i], terms[i + sz / 2]};
      FastTerm term = newFuncTerm(f, args);
      terms[i] = term;
    }

  return terms[0];
}

FastTerm constructFastTerm(int n, int* a, int* b) {
  vector<pair<int, vector<FastTerm>>> stk;
  vector<FastSort> sorts(n / 2, fastStateSort());
  for (int i = 0; i < n - 1; ++i) {
    if (b[i] == kTypeNoType) {
      auto index = stk.back().first;
      auto terms = stk.back().second;
      FastTerm t = combineTerms(kNameConvert[b[index]] + to_string(a[index]), b[index], terms, sorts);
      stk.pop_back();
      stk.back().second.emplace_back(t);
      continue;
    }
    if (b[i] == kTypeConst) {
      string name = kNameConvert[b[i]] + to_string(a[i]);
      if (!existsFunc(name.c_str())) newConst(name.c_str(), fastStateSort());
      FastFunc f = getFuncByName(name.c_str());
      FastTerm t = newFuncTerm(f, nullptr);
      if (!stk.size()) return t;
      stk.back().second.emplace_back(t);
      ++i;
      continue;
    }
    if (b[i] == kTypeVar) {
      string name = kNameConvert[b[i]] + to_string(a[i]);
      if (!existsVar(name.c_str())) newVar(name.c_str(), fastStateSort());
      FastTerm var = static_cast<FastTerm>(getVarByName(name.c_str()));
      if (!stk.size()) return var;
      stk.back().second.emplace_back(var);
      ++i;
      continue;
    }
    stk.emplace_back(i, vector<FastTerm>());
  }
  assert(stk.size() == 1);
  auto index = stk.back().first;
  auto terms = stk.back().second;
  return combineTerms(kNameConvert[b[index]] + to_string(a[index]), b[index], terms, sorts);
}

void printPreorder(int n, int* a, int* b) {
  cout << "Cpp Func: ";
  for (int i = 0; i < n; ++i) 
    cout << "(" << a[i] << ", " << b[i] << ')' << " \n"[i == n - 1];
  FastTerm term = constructFastTerm(n, a, b);
  cout << toString(term) << '\n';
}