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
#include "solver.h"
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
      std::shared_ptr<BoolectorSortBase> bs = std::static_pointer_cast<BoolectorSortBase>(sort);
      Term term(new BoolectorTerm(btor,
                                  boolector_var(btor, bs->sort, name.c_str()),
                                  std::vector<Term>{},
                                  VAR));
      return term;
    }
    void assert_formula(Term& t) const override
    {
      std::shared_ptr<BoolectorTerm> bt = std::static_pointer_cast<BoolectorTerm>(t);
      boolector_assert(btor, bt->node);
    }
    bool check_sat() const override { return boolector_sat(btor); };
    // TODO: Implement this
    Term get_value(Term& t) const override {};
    Sort construct_sort(Kind k) const override
    {
      if (k == BOOL)
      {
        Sort s(new BoolectorBVSort(btor, boolector_bool_sort(btor), 1));
        return s;
      }
      else
      {
        std::string msg("Boolector does not support ");
        msg += to_string(k);
        throw NotImplementedException(msg.c_str());
      }
    }
    Sort construct_sort(Kind k, unsigned int size) const override
    {
      if (k == BV)
        {
          Sort s(new BoolectorBVSort(btor, boolector_bitvec_sort(btor, size), size));
          return s;
        }
      else
        {
          std::string msg("Can't create Kind ");
          msg += to_string(k);
          msg += " with int argument.";
          throw IncorrectUsageException(msg.c_str());
        }
    }
    Sort construct_sort(Kind k, Sort idxsort, Sort elemsort) const override
    {
      if (k == ARRAY)
      {
        std::shared_ptr<BoolectorSortBase> btor_idxsort = std::static_pointer_cast<BoolectorSortBase>(idxsort);
        std::shared_ptr<BoolectorSortBase> btor_elemsort = std::static_pointer_cast<BoolectorSortBase>(elemsort);
        BoolectorSort bs = boolector_array_sort(btor, btor_idxsort->sort, btor_elemsort->sort);
        Sort s(new BoolectorArraySort(btor, bs, idxsort, elemsort));
        return s;
      }
      else
      {
        std::string msg("Can't create Kind ");
        msg += to_string(k);
        msg += " with two sort arguments.";
        throw IncorrectUsageException(msg.c_str());
      }
    }
    Sort construct_sort(Kind k, std::vector<Sort> sorts, Sort sort) const override
    {
      if (k == UNINTERPRETED)
        {
          int arity = sorts.size();
          std::vector<BoolectorSort> btor_sorts(arity);
          for (auto s : sorts)
          {
            std::shared_ptr<BoolectorSortBase> bs = std::static_pointer_cast<BoolectorSortBase>(s);
            btor_sorts.push_back(bs->sort);
          }
          std::shared_ptr<BoolectorSortBase> btor_sort = std::static_pointer_cast<BoolectorSortBase>(sort);
          BoolectorSort btor_fun_sort = boolector_fun_sort(btor, &btor_sorts[0], arity, btor_sort->sort);
          Sort s(new BoolectorFunctionSort(btor, btor_fun_sort, sorts, sort));
          return s;
        }
      else
        {
          std::string msg("Can't create Kind ");
          msg += to_string(k);
          msg += " with a vector of sorts and a sort";
          throw IncorrectUsageException(msg.c_str());
        }
    }
    // TODO: Implement the two apply_op methods
    Term apply_op(PrimOp op, std::vector<Term> terms) const override {};
    Term apply_op(Op op, std::vector<Term> terms) const override {};
  protected:
    Btor * btor;
  };
}

#endif
