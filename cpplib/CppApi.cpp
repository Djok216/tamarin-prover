#include "CppApi.h"
#include <iostream>
#include <vector>
#include <tuple>
#include <cassert>
#include <cstring>
#include <map>
#include "fastterm.h"
#include "fastqueryacunify.h"
using namespace std;

constexpr int kEncodingEnd = -4;
constexpr int kOneVarSubstEnd = -3;
constexpr int kSubstEnd = -2;
constexpr int kTypeNoType = -1;
constexpr int kTypeConst = 0;
constexpr int kTypeVar = 1;
constexpr int kTypeNoEq = 2;
constexpr int kTypeAC = 3;
constexpr int kTypeC = 4;
constexpr int kTypeList = 5;

constexpr int kNumbOfTypes = 6;

constexpr const char* kNameConvert[kNumbOfTypes] = 
    {"HsConst", "HsVar", "HsNoEqf", "HsACf", "HsCf", "HsListf"};
constexpr size_t kNameConvertSize[kNumbOfTypes] =
    {
    strlen(kNameConvert[kTypeConst]), strlen(kNameConvert[kTypeVar]),
    strlen(kNameConvert[kTypeNoEq]), strlen(kNameConvert[kTypeAC]),
    strlen(kNameConvert[kTypeC]), strlen(kNameConvert[kTypeList])
    };

map<FastTerm, int> mapper;
int mapperOffset;
vector<int> encodedss;

int mapperGet(FastTerm term) {
  if (mapper.count(term)) return mapper[term];
  int val = mapperOffset + mapper.size();
  return mapper[term] = val;
}

bool startsWith(const string& a, const string& b) {
  if (b.size() < a.size()) return false;
  for (int i = 0; i < b.size(); ++i) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

int getTermEncoding(FastTerm term) {
  if (isVariable(term)) {
    string name = getVarName(term);
    if (startsWith(name, kNameConvert[kTypeVar])) {
      return stoi(name.substr(kNameConvertSize[kTypeVar]));
    }
    return mapperGet(term);
  }
  string name = getFuncName(getFunc(term));
  for (int i = 0; i < kNumbOfTypes; ++i) {
    if (startsWith(name, kNameConvert[i])) {
      return stoi(name.substr(kNameConvertSize[i]));
    }
  }
  return mapperGet(term);
}

FastTerm combineTerms(
    const string& name,
    int type, 
    vector<FastTerm>& terms, 
    vector<FastSort>& sorts) {
  FastFunc f;
  if (existsFunc(name.c_str())) f = getFuncByName(name.c_str());
  else {
    if (type != kTypeAC) {
      f = newFunc(name.c_str(), fastStateSort(), terms.size(), &sorts[0]);
      return newFuncTerm(f, &terms[0]);
    }
    f = newACFunc(name.c_str(), fastStateSort());
  }
  for (int sz = 2; sz / 2 < terms.size(); sz *= 2)
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
      FastTerm t = combineTerms(
                      kNameConvert[b[index]] + to_string(a[index]),
                      b[index], terms, sorts);
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
  return combineTerms(
            kNameConvert[b[index]] + to_string(a[index]),
            b[index], terms, sorts);
}

void preorder(FastTerm term) {
  encodedss.push_back(mapperGet(term));
  if (isFuncTerm(term)) {
    int arity = getArity(getFunc(term));
    for (int i = 0; i < arity; ++i) preorder(getArg(term, i));
  }
  encodedss.push_back(kTypeNoType);
}

// var -> term is encoded as
// [f(var), preorder(term), f(var), preorder(term), ..., kSubstEnd]
void encodeSubstSet(const vector<FastSubst>& substSet) {
  encodedss.clear();
  for (const auto& subst : substSet) {
    for (int i = 0; i < subst.count; i += 2) {
      FastVar var = subst.data[i];
      FastTerm term = subst.data[i + 1];
      encodedss.push_back(mapperGet(var));
      preorder(term);
      encodedss.push_back(kOneVarSubstEnd);
    }
    encodedss.push_back(kSubstEnd);
  }
  encodedss.push_back(kEncodingEnd);
}

int* printSubstitutions(int n1, int* a1, int* b1, int n2, int* a2, int* b2) {
  mapper.clear();
  mapperOffset = n1 / 2 + n2 / 2 + 1;
  FastTerm t1 = constructFastTerm(n1, a1, b1);
  FastTerm t2 = constructFastTerm(n2, a2, b2);
  FastQueryACUnify solver(t1, t2);
  auto substSet = solver.solve();
  encodeSubstSet(substSet);
  return encodedss.data();
}