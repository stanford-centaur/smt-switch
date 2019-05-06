#include "assert.h"
#include <iostream>
#include <memory>
#include <vector>

#include "boolector/boolector.h"

#include "boolector_solver.h"
#include "boolector_sort.h"
#include "boolector_term.h"
#include "op.h"

using namespace smt;
using namespace std;

bool term_creation() {
  bool res = true;
  Btor *btor = boolector_new();
  boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);

  BoolectorSort bvsort8 = boolector_bitvec_sort(btor, 8);

  BoolectorNode *x = boolector_var(btor, bvsort8, "x");
  BoolectorNode *y = boolector_var(btor, bvsort8, "y");
  BoolectorNode *x_ulte_y = boolector_ulte(btor, x, y);

  Term bx = make_shared<BoolectorTerm>(
      btor, x, std::vector<Term>{}, VAR);

  Term by = make_shared<BoolectorTerm>(
      btor, y, std::vector<Term>{}, VAR);
  Term bx_ule_y = make_shared<BoolectorTerm>(
      btor, x_ulte_y, std::vector<Term>{bx, by}, BVULE);

  try {
    Sort sort = bx_ule_y->get_sort();
    res = false;
  } catch (NotImplementedException &e) {
    res = true;
  }

  Op op = bx_ule_y->get_op();
  res &= (get<PrimOp>(op) == BVULE);
  res &= (to_string(get<PrimOp>(op)) == "BVULE");

  res &= !(bx->compare(by));
  Term bx_ule_y_copy = bx_ule_y;
  res &= (bx_ule_y_copy->compare(bx_ule_y));
  res &= (bx_ule_y_copy == bx_ule_y);
  // note: I overloaded operator== for Term (aka shared_ptr<AbsTerm>) so that the following code works
  //       it uses 'compare' under the hood
  boolector_copy(btor, x_ulte_y);
  Term bx_ule_y_copy2 = make_shared<BoolectorTerm>(btor, x_ulte_y, vector<Term>{bx, by}, BVULE);
  res &= (bx_ule_y_copy == bx_ule_y_copy2);

  boolector_release_sort(btor, bvsort8);
  // TODO handle the memory leak issue
  //      can't delete the btor object because need it in BoolectorTerm
  //      destructors
  return res;
}

bool sorts()
{
  bool res = true;
  Btor *btor = boolector_new();
  boolector_set_opt(btor, BTOR_OPT_MODEL_GEN, 1);

  BoolectorSort bvsort8 = boolector_bitvec_sort(btor, 8);
  Sort s(new BoolectorBVSort(btor, bvsort8, 8));
  BoolectorSort bvsort8_2 = boolector_bitvec_sort(btor, 8);
  Sort s2(new BoolectorBVSort(btor, bvsort8_2, 8));
  res &= (s == s2);

  BoolectorSort btor_arr_sort = boolector_array_sort(btor, bvsort8, bvsort8);
  Sort arr_sort(new BoolectorArraySort(btor, btor_arr_sort, s, s2));
  Sort arr_sort_copy;
  arr_sort_copy = arr_sort;
  res &= (arr_sort == arr_sort_copy);
  res &= (arr_sort->get_indexsort() == s);
  res &= (arr_sort->get_elemsort() == s2);
  // index and elem sorts happen to be the same
  res &= (arr_sort->get_elemsort() == s);
  return res;
}

bool solver()
{
  bool res = true;
  // Solver s (new BoolectorSolver());
  Solver s = make_shared<BoolectorSolver>();
}

int main() {
  assert(term_creation());
  assert(sorts());
}
