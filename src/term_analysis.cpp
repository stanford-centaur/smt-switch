/*!
 * \file term_analysis.cpp
 * \brief Theory atoms of formulas and the symbols that justify a model value
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * It defines AbsSmtSolver::get_theory_atoms and
 * AbsSmtSolver::get_justifying_symbols.
 */
#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "smt-switch/ops.h"
#include "smt-switch/smt_defs.h"
#include "smt-switch/solver.h"
#include "smt-switch/sort.h"
#include "smt-switch/term.h"
#include "smt-switch/term_visitor.h"

namespace smt {

namespace {

// Collects the theory atoms of a formula, going through its connectives.
// With split_ites, an application with if-then-else children is visited
// once for each choice of their branches, and their conditions too.
class TheoryAtomsVisitor : public TermVisitor
{
 public:
  TheoryAtomsVisitor(std::shared_ptr<const AbsSmtSolver> solver,
                     bool split_ites,
                     UnorderedTermSet & out)
      : solver_(solver),
        boolsort_(solver->make_sort(BOOL)),
        split_ites_(split_ites),
        out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    if (term->get_sort() != boolsort_ || term->is_value())
    {
      return VisitResult::Skip;
    }
    if (split_ites_)
    {
      // each child's choices: both branches of an if-then-else, else itself
      std::vector<TermVec> choices;
      bool has_ite = false;
      for (const Term & c : term)
      {
        if (c->get_op() == Ite)
        {
          has_ite = true;
          TermVec ite(c->begin(), c->end());
          visit(ite[0]);
          choices.push_back({ ite[1], ite[2] });
        }
        else
        {
          choices.push_back({ c });
        }
      }
      if (has_ite)
      {
        // count through every combination of choices, the first fastest
        std::vector<std::size_t> picks(choices.size(), 0);
        std::size_t i = 0;
        while (i < picks.size())
        {
          TermVec children;
          for (std::size_t j = 0; j < choices.size(); ++j)
          {
            children.push_back(choices[j][picks[j]]);
          }
          visit(solver_->make_term(term->get_op(), children));
          for (i = 0; i < picks.size() && ++picks[i] == choices[i].size(); ++i)
          {
            picks[i] = 0;
          }
        }
        return VisitResult::Continue;
      }
    }
    if (term->is_theory_atom(boolsort_))
    {
      out_.insert(term);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  std::shared_ptr<const AbsSmtSolver> solver_;
  Sort boolsort_;
  bool split_ites_;
  UnorderedTermSet & out_;
};

// Collects the symbolic constants that fix the values of terms in the
// model, following only the child that decides a term's value when one
// does
class JustificationVisitor : public TermVisitor
{
 public:
  JustificationVisitor(std::shared_ptr<const AbsSmtSolver> solver,
                       UnorderedTermSet & out)
      : solver_(solver), out_(out)
  {
  }

 protected:
  VisitResult visit_term(const Term & term) override
  {
    Op op = term->get_op();
    if (op.is_null())
    {
      if (term->is_symbolic_const())
      {
        out_.insert(term);
      }
      return VisitResult::Skip;
    }
    TermVec children(term->begin(), term->end());
    if (op == Ite)
    {
      visit(children[0]);
      visit(solver_->get_value(children[0])->to_bool() ? children[1]
                                                       : children[2]);
      return VisitResult::Skip;
    }
    Term decider;
    if (op == And || op == Or)
    {
      // a false conjunct or a true disjunct
      bool deciding_value = op == Or;
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bool() == deciding_value)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == Implies)
    {
      // a false premise, else a true conclusion
      for (std::size_t i = 0; i + 1 < children.size() && !decider; ++i)
      {
        if (!solver_->get_value(children[i])->to_bool())
        {
          decider = children[i];
        }
      }
      if (!decider && solver_->get_value(children.back())->to_bool())
      {
        decider = children.back();
      }
    }
    else if (op == BVAnd || op == BVNand || op == BVMul)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('1') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    else if (op == BVOr || op == BVNor)
    {
      for (const Term & c : children)
      {
        if (solver_->get_value(c)->to_bits().find('0') == std::string::npos)
        {
          decider = c;
          break;
        }
      }
    }
    if (decider)
    {
      visit(decider);
      return VisitResult::Skip;
    }
    return VisitResult::Continue;
  }

 private:
  std::shared_ptr<const AbsSmtSolver> solver_;
  UnorderedTermSet & out_;
};

}  // namespace

void AbsSmtSolver::get_theory_atoms(const Term & formula,
                                    UnorderedTermSet & out,
                                    bool split_ites) const
{
  TheoryAtomsVisitor(shared_from_this(), split_ites, out).visit(formula);
}

void AbsSmtSolver::get_justifying_symbols(const Term & term,
                                          UnorderedTermSet & out) const
{
  JustificationVisitor(shared_from_this(), out).visit(term);
}

}  // namespace smt
