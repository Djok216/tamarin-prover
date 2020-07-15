#include "CppApi.h"
#include <iostream>
#include <vector>
#include <tuple>
#include <cassert>
#include <cstring>
#include <map>
#include "UnifLib216.h"
using namespace std;

constexpr int kEndOfEncodedTerm = -5;
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
constexpr int kSortPub = 7;
constexpr int kSortFresh = 8;
constexpr int kSortMsg = 9;
constexpr int kSortNode = 10;

constexpr const char* kNameConvert[kNumbOfTypes] = 
    {"HsConst", "HsVar", "HsNoEqf", "HsACf", "HsCf", "HsListf"};
constexpr size_t kNameConvertSize[kNumbOfTypes] =
    {
    strlen(kNameConvert[kTypeConst]), strlen(kNameConvert[kTypeVar]),
    strlen(kNameConvert[kTypeNoEq]), strlen(kNameConvert[kTypeAC]),
    strlen(kNameConvert[kTypeC]), strlen(kNameConvert[kTypeList])
    };

map<int, FastSort> mapSorts;
map<FastTerm, int> mapper;
int unifProblemsCounter;
int maxVariableId;
vector<int> encodedss;

int mapperGet(FastTerm term) {
  if (mapper.count(term)) return mapper[term];
  int val = mapper.size() + maxVariableId + 1;
  if (getSort(term) == mapSorts[kSortFresh]) val *= -1;
  return mapper[term] = val;
}

bool startsWith(const string& a, const string& b) {
  if (b.size() > a.size()) return false;
  for (int i = 0; i < b.size(); ++i) {
    if (a[i] != b[i]) return false;
  }
  return true;
}

int getNumber(const string& s) {
  string cs = s;
  if (unifProblemsCounter == 0) cs.pop_back();
  for (int aux = unifProblemsCounter; aux; aux /= 10) cs.pop_back();
  cs.pop_back();
  return stoi(cs);
}

int getTermEncoding(FastTerm term) {
  if (isVariable(term)) {
    string name = getVarName(term);
    if (startsWith(name, kNameConvert[kTypeVar])) {
      return getNumber(name.substr(kNameConvertSize[kTypeVar]));
    }
    return mapperGet(term);
  }
  string name = getFuncName(getFunc(term));
  for (int i = 0; i < kNumbOfTypes; ++i) {
    if (startsWith(name, kNameConvert[i])) {
      return getNumber(name.substr(kNameConvertSize[i]));
    }
  }
  return mapperGet(term);
}

FastTerm combineTerms(
    const string& name,
    int type, 
    vector<FastTerm>& terms) {
  FastFunc f;
  if (existsFunc(name.c_str())) f = getFuncByName(name.c_str());
  else {
    switch (type) {
      case kTypeAC:
        f = newACFunc(name.c_str(), mapSorts[kSortMsg]);
        break;
      case kTypeC:
        f = newCFunc(name.c_str(), mapSorts[kSortMsg]);
        break;
      case kTypeList:
      case kTypeNoEq: {
        vector<FastSort> sorts(terms.size());
        for (int i = 0; i < sorts.size(); ++i) sorts[i] = getSort(terms[i]);
        f = newFunc(name.c_str(), mapSorts[kSortMsg], terms.size(), &sorts[0]);
        break;
      }
      default:
        cerr << "WRONG TYPE!\n";
        exit(1);
    }
  }

  if (type != kTypeAC && type != kTypeC) return newFuncTerm(f, &terms[0]);
  for (int sz = 2; sz / 2 < terms.size(); sz *= 2)
    for (int i = 0; i + sz / 2 < terms.size(); i += sz) {
      FastTerm args[2] = {terms[i], terms[i + sz / 2]};
      FastTerm term = newFuncTerm(f, args);
      terms[i] = term;
    }
  return terms[0];
}

FastTerm constructFastTerm(int n, int* a, int* b, int* c) {
  vector<pair<int, vector<FastTerm>>> stk;
  for (int i = 0; i < n - 1; ++i) {
    if (b[i] == kTypeNoType) {
      auto index = stk.back().first;
      auto terms = stk.back().second;
      FastTerm t = combineTerms(
                      kNameConvert[b[index]] + to_string(a[index]) + "#" + to_string(unifProblemsCounter),
                      b[index], terms);
      stk.pop_back();
      stk.back().second.emplace_back(t);
      continue;
    }
    if (b[i] == kTypeConst) {
      string name = kNameConvert[b[i]] + to_string(a[i]) + "#" + to_string(unifProblemsCounter);
      if (!existsFunc(name.c_str())) newConst(name.c_str(), mapSorts[c[i]]);
      FastFunc f = getFuncByName(name.c_str());
      FastTerm t = newFuncTerm(f, nullptr);
      if (!stk.size()) return t;
      stk.back().second.emplace_back(t);
      ++i;
      continue;
    }
    if (b[i] == kTypeVar) {
      string name = kNameConvert[b[i]] + to_string(a[i]) + "#" + to_string(unifProblemsCounter);
      maxVariableId = max(maxVariableId, a[i]);
      if (!existsVar(name.c_str())) newVar(name.c_str(), mapSorts[c[i]]);
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
  string finalName = kNameConvert[b[index]] + to_string(a[index]) + "#" + to_string(unifProblemsCounter);
  return combineTerms(finalName, b[index], terms);
}

void preorder(FastTerm term) {
  encodedss.push_back(getTermEncoding(term));
  if (isFuncTerm(term)) {
    int arity = getArity(getFunc(term));
    for (int i = 0; i < arity; ++i) {
      auto arg = getArg(term, i);
      if (isFuncTerm(arg) && getFunc(arg) == getFunc(term) && isFuncAC(getFunc(term))) {
        preorder(getArg(arg, 0));
        preorder(getArg(arg, 1));
      } else {
        preorder(getArg(term, i));
      }
    }
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
      encodedss.push_back(getTermEncoding(var));
      preorder(term);
      encodedss.push_back(kOneVarSubstEnd);
    }
    encodedss.push_back(kSubstEnd);
  }
  encodedss.push_back(kEncodingEnd);
}

int* printSubstitutions(int n1, int* a1, int* b1, int* c1, int n2, int* a2, int* b2, int* c2) {
  mapper.clear();
  maxVariableId = 0;
  static bool initHsSorts = false;
  if (!initHsSorts) {
    initHsSorts = true;
    mapSorts[kSortPub] = newSort("LSortPub");
    mapSorts[kSortFresh] = newSort("LSortFresh");
    mapSorts[kSortMsg] = newSort("LSortMsg");
    mapSorts[kSortNode] = newSort("LSortNode");
    newSubSort(mapSorts[kSortFresh], mapSorts[kSortMsg]);
    newSubSort(mapSorts[kSortPub], mapSorts[kSortMsg]);
  }
  /*
  vector<FastSubst> aasdadasd;
  encodeSubstSet(aasdadasd);
  if (unifProblemsCounter > 0) return encodedss.data();
  */
  UnifEqSystem ues;
  for (int i = 0; i < n1; ++i, ++a1, ++a2, ++b1, ++b2, ++c1, ++c2) {
    int n11 = 0, n22 = 0;
    for (n11 = 0; a1[n11] != kEndOfEncodedTerm; ++n11);
    for (n22 = 0; a2[n22] != kEndOfEncodedTerm; ++n22);
    FastTerm t1 = constructFastTerm(n11, a1, b1, c1);
    FastTerm t2 = constructFastTerm(n22, a2, b2, c2);
    while (n11--) ++a1, ++b1, ++c1, ++i;
    while (n22--) ++a2, ++b2, ++c2;
    ues.addEq(UnifEq(t1, t2), true);
  }/*
  vector<FastSubst> fakeSubst;
  // {BBx.10 <~ HsVar4#0, HsACf0#0(AAx.9,BBx.12,HsNoEqf1#0(AAx.13)) <~ HsVar3#0, AAx.11 <~ HsVar2#0, BBx.12 <~ HsVar7#0, HsACf0#0(AAx.9,BBx.10,HsNoEqf1#0(AAx.11)) <~ HsVar6#0, AAx.13 <~ HsVar5#0}
  FastTerm args[2];
  FastVar bbx10 = createFreshVariable(mapSorts[kSortFresh]); mapper[bbx10] = -10;
  FastVar aax9 = createFreshVariable(mapSorts[kSortMsg]); mapper[aax9] = 9;
  FastVar bbx12 = createFreshVariable(mapSorts[kSortFresh]); mapper[bbx12] = -12;
  FastVar aax13 = createFreshVariable(mapSorts[kSortMsg]); mapper[aax13] = 13;
  FastVar aax11 = createFreshVariable(mapSorts[kSortMsg]); mapper[aax11] = 11;
  FastVar aax10 = createFreshVariable(mapSorts[kSortMsg]); mapper[aax10] = 10;
  FastVar aax12 = createFreshVariable(mapSorts[kSortMsg]); mapper[aax12] = 12;
  FastVar bbx11 = createFreshVariable(mapSorts[kSortFresh]); mapper[bbx11] = -11;
  FastVar bbx9 = createFreshVariable(mapSorts[kSortFresh]); mapper[bbx9] = -9;
  FastFunc h = getFuncByName("HsNoEqf1#0");
  FastFunc Xor = getFuncByName("HsACf0#0");
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx10);
  args[0] = aax9; args[1] = bbx12; FastTerm aux = newFuncTerm(Xor, args); args[0] = aax13; FastTerm haax13 = newFuncTerm(h, args); args[0] = aux; args[1] = haax13; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax11);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx12);
  args[0] = aax9; args[1] = bbx10; aux = newFuncTerm(Xor, args); args[0] = aax11; FastTerm haax11 = newFuncTerm(h, args); args[0] = aux; args[1] = haax11; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax13);

  // {BBx.10 <~ HsVar4#0, HsACf0#0(AAx.9,BBx.11) <~ HsVar3#0, AAx.12 <~ HsVar2#0, BBx.11 <~ HsVar7#0, HsACf0#0(AAx.9,BBx.10) <~ HsVar6#0, AAx.12 <~ HsVar5#0}
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx10);
  args[0] = aax9; args[1] = bbx11; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax12);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx11);
  args[0] = aax9; args[1] = bbx10; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax12);

  // {BBx.11 <~ HsVar4#0, HsACf0#0(AAx.9,HsNoEqf1#0(AAx.12)) <~ HsVar3#0, AAx.10 <~ HsVar2#0, BBx.11 <~ HsVar7#0, HsACf0#0(AAx.9,HsNoEqf1#0(AAx.10)) <~ HsVar6#0, AAx.12 <~ HsVar5#0}
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx11);
  args[0] = aax12; aux = newFuncTerm(h, args); args[0] = aax9; args[1] = aux; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax10);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx11);
  args[0] = aax10; aux = newFuncTerm(h, args); args[0] = aax9; args[1] = aux; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax12);

  // {BBx.10 <~ HsVar4#0, AAx.9 <~ HsVar3#0, AAx.11 <~ HsVar2#0, BBx.10 <~ HsVar7#0, AAx.9 <~ HsVar6#0, AAx.11 <~ HsVar5#0}
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx10);
  fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aax9);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax11);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx10);
  fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aax9);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax11);

  // {BBx.9 <~ HsVar4#0, HsACf0#0(BBx.11,HsNoEqf1#0(AAx.12)) <~ HsVar3#0, AAx.10 <~ HsVar2#0, BBx.11 <~ HsVar7#0, HsACf0#0(BBx.9,HsNoEqf1#0(AAx.10)) <~ HsVar6#0, AAx.12 <~ HsVar5#0}
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx9);
  args[0] = aax12; aux = newFuncTerm(h, args); args[0] = bbx11; args[1] = aux; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax10);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx11);
  args[0] = aax10; aux = newFuncTerm(h, args); args[0] = bbx9; args[1] = aux; aux = newFuncTerm(Xor, args); fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax12);
  
  // {BBx.9 <~ HsVar4#0, BBx.10 <~ HsVar3#0, AAx.11 <~ HsVar2#0, BBx.10 <~ HsVar7#0, BBx.9 <~ HsVar6#0, AAx.11 <~ HsVar5#0}
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx9);
  fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), bbx10);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax11);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx10);
  fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), bbx9);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax11);

  // {BBx.10 <~ HsVar4#0, HsNoEqf1#0(AAx.11) <~ HsVar3#0, AAx.9 <~ HsVar2#0, BBx.10 <~ HsVar7#0, HsNoEqf1#0(AAx.9) <~ HsVar6#0, AAx.11 <~ HsVar5#0}]
  fakeSubst.emplace_back(FastSubst());
  fakeSubst.back().addToSubst(getVarByName("HsVar4#0"), bbx10);
  args[0] = aax11; aux = newFuncTerm(h, args); fakeSubst.back().addToSubst(getVarByName("HsVar3#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar2#0"), aax9);
  fakeSubst.back().addToSubst(getVarByName("HsVar7#0"), bbx10);
  args[0] = aax9; aux = newFuncTerm(h, args); fakeSubst.back().addToSubst(getVarByName("HsVar6#0"), aux);
  fakeSubst.back().addToSubst(getVarByName("HsVar5#0"), aax11);

  encodeSubstSet(fakeSubst);
  ++unifProblemsCounter;
  return encodedss.data();
  */
  FastQueryACUnify solver(0, 0);
  auto substSet = solver.solve(ues);
  for (auto& subst : substSet) {
    for (int i = 0; i < subst.count; i += 2) {
      FastVar var = subst.data[i];
      if (occurs(var, ues[0].t1)) continue;
      if (occurs(var, ues[0].t2)) continue;
      bool flag = false;
      for (int j = 0; j < subst.count && !flag; j += 2) {
        if (i == j) continue;
        if (occurs(var, subst.data[i + 1])) flag = true;
      }
      if (flag == false) {
        swap(subst.data[i], subst.data[subst.count - 2]);
        swap(subst.data[i + 1], subst.data[subst.count - 1]);
        subst.count -= 2;
        i -= 2;
      }
    }
  }
  encodeSubstSet(substSet);
  ++unifProblemsCounter;
  return encodedss.data();
}