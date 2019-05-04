#ifndef SMT_BOOLECTOR_SOLVER_H
#define SMT_BOOLECTOR_SOLVER_H

#include <memory>
#include <string>
#include <vector>

#include "exceptions.h"
#include "boolector_function.h"
#include "boolector_op.h"
#include "boolector_sort.h"
#include "boolector_term.h"
#include "sort.h"

namespace smt
{
  /**
     Boolector Solver implementation
   */
  class BoolectorSolver : public AbsSolver
  {
  public:
    // might have to use std::unique_ptr<Btor>(boolector_new) and move it?
    BoolectorSolver() : btor(boolector_new()) {};
    BoolectorSolver(const BoolectorSolver&) = delete;
    BoolectorSolver& operator=(const BoolectorSolver&) = delete;
    ~BoolectorSolver() { boolector_delete(btor); };
    Sort declare_sort(const std::string name, unsigned int arity) const override
    {
      throw IncorrectUsageException("Can't declare sorts with Boolector");
    }
    Term declare_const(const std::string name, Sort sort) const override
    {
      std::shared_ptr<BoolectorSort> bs = std::static_pointer_cast<BoolectorSort>(s);
      std::shared_ptr<Term> term(new BoolectorTerm(btor,
                                                   boolector_var(btor, bs->sort, name),
                                                   std::vector<Term>{},
                                                   VAR));
      return term;
    }
    void assert(Term& t) const override
    {
      std::shared_ptr<BoolectorTerm> bt = std::static_pointer_cast<BoolectorTerm>(t);
      boolector_assert(btor, bt->node);
    }
    bool check_sat() const override { return boolector_sat(btor); };
    // TODO: Implement this
    // Term get_value(Term& t) const override {};
    Sort construct_sort(Kind k) const override
    {
      if (k == BOOL)
      {
        Sort s(new BoolectorBVSort(k, btor, boolector_bool_sort(btor), 1));
        return s;
      }
      else
      {
        throw NotImplementedException("Boolector does not support " + to_string(k));
      }
    }
    Sort construct_sort(Kind k, unsigned int size) const override
    {
      if (k == BV)
        {
          Sort s(new BoolectorBVSort(k, btor, boolector_bitvec_sort(btor, size), size));
          return s;
        }
      else
        {
          throw IncorrectUsageException("Can't create Kind " + to_string(k) + " with int argument.");
        }
    }
    Sort construct_sort(Kind k, Sort idxsort, Sort elemsort) const override
    {
      if (k == ARRAY)
      {
        std::shared_ptr<BoolectorSort> btor_idxsort = std::static_pointer_cast<BoolectorSort>(idxsort);
        std::shared_ptr<BoolectorSort> btor_elemsort = std::static_pointer_cast<BoolectorSort>(elemsort);
        BoolectorSort bs = boolector_array_sort(btor, btor_idxsort->sort, btor_elemsort->sort);
        Sort s(new BoolectorArraySort(k, btor, bs, idxsort, elemsort));
        return s;
      }
      else
      {
        throw IncorrectUsageException("Can't create Kind " + to_string(k) + " with two sort arguments.");
      }
    }
    Sort construct_sort(Kind k, std::vector<Sort> sorts, Sort sort) const override
    {
      if (k == UNINTERPRETED)
        {
          std::vector<BoolectorSort> btor_sorts(sorts.size());
          for (auto s : sorts)
          {
            BoolectorSort bs = std::static_cast<BoolectorSort>(*s);
            btor_sorts.push_back(s);
          }
          std::shared_ptr<BoolectorSort> btor_sort = std::static_pointer_cast<BoolectorSort>(sort);
          BoolectorSort bs = boolector_fun_sort(btor, &btor_sorts[0], btor_sort->sort);
          Sort s(new BoolectorFunctionSort(k, btor, bs, sorts, sort));
          return s;
        }
      else
        {
          throw IncorrectUsageException("Can't create Kind " + to_string(k) + " with a vector of sorts and a sort");
        }
    }
    // TODO: Implement the two apply_op methods
    // Term apply_op(PrimOp op, std::vector<Term> terms) const override {};
    // Term apply_op(Op op, std::vector<Term> terms) const override {};
  protected:
    Btor * btor;
  };
}

#endif
