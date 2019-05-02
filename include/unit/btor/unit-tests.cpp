#include "assert.h"
#include <iostream>
#include <memory>
#include <vector>

#include "boolector/boolector.h"
#include "boolector_term.h"
#include "op.h"
#include "sort.h"
#include "term.h"

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

  Term bx_ule_y_copy = bx_ule_y;
  res &= (bx_ule_y_copy->compare(bx_ule_y));
  res &= (bx_ule_y_copy == bx_ule_y);
  // note, if we made another bx_ule_y_copy term using make_shared with the same args and compared them,
  //       we would get false. because the shared_ptr only compares the pointer values
  // haven't figured out if this is a problem yet
  // For example, the code below prints 0
  // Term bx_ule_y_copy2 = make_shared<BoolectorTerm>(btor, x_ulte_y, vector<Term>{bx, by}, BVULE);
  // cout << (bx_ule_y_copy == bx_ule_y_copy2) << endl;
  res &= !(bx->compare(by));

  boolector_release_sort(btor, bvsort8);
  // TODO handle the memory leak issue
  //      can't delete the btor object because need it in BoolectorTerm
  //      destructors
  return res;
}

int main() { assert(term_creation()); }
