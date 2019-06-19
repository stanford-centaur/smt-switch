#ifndef SMT_CVC4_FUN_H
#define SMT_CVC4_FUN_H

#include "exceptions.h"

#include "api/cvc4cpp.h"

namespace smt {
  class CVC4Fun : public AbsFun
  {
  public:
    CVC4Fun(::CVC4::api::Term fun) : fun(fun), is_uf(true), indexed(false) {}
    CVC4Fun(::CVC4::api::Kind kind) : kind(kind), is_uf(false), indexed(false) {}
    CVC4Fun(::CVC4::api::OpTerm o) : op(o), is_uf(false), indexed(true) {}
    bool is_uf() const override;
    bool is_op() const override;
    Sort get_sort() const override;
    Op get_op() const override;
    std::string get_name() const override;
  protected:
    ::CVC4::api::Term fun;
    ::CVC4::api::Kind kind;
    ::CVC4::api::OpTerm op;
    // true if this Fun holds an uninterpreted function (CVC4::api::Term)
    bool is_uf;
    // only relevant if is_uf is false, says whether this Fun holds a kind or opterm
    bool indexed;
}

#endif
