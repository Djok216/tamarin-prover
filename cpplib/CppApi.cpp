#include <iostream>
#include "CppApi.h"

using std::cout;

void printPreorder(int n, int* a, int* b) {
  cout << "Cpp Func: ";
  for (int i = 0; i < n; ++i) 
    cout << "(" << a[i] << ", " << b[i] << ')' << " \n"[i == n - 1];
}