/*********************                                                        */
/*! \file z3_sort.h
** \verbatim
** Top contributors (to current version):
**   Lindsey Stuntz
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Z3 implementation of AbsSort
**
**
**/

#pragma once

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

#include "z3++.h"

using namespace z3;
namespace smt {

// forward declaration
class Z3Solver;

class Z3Sort : public AbsSort
{
 public:
  // Non-functions
  Z3Sort(sort z3sort) : type(z3sort), is_function(false){
//	  context c;
//	  z_func = func_decl(ctx);
  };

  // Functions
   Z3Sort(sort z3sort, bool is_fun, func_decl zfunc) :
	   type(z3sort), is_function(is_fun){//, z_func(zfunc){
	   z_func = &zfunc;
   };

   Z3Sort(sort z3sort, bool tmp, bool is_fun, func_decl zfunc) :
	   type(z3sort), is_function(is_fun), zsort(zfunc) {
//	   new (zsort.f) = zfunc;
//	   zsort f = &zfunc;
   };

//   Z3Sort(sort z3sort, bool t) : type(z3sort), is_function(false){
//	   test a = t;
//     };

  ~Z3Sort() = default;
  std::size_t hash() const override;
  uint64_t get_width() const override;
  Sort get_indexsort() const override;
  Sort get_elemsort() const override;
  SortVec get_domain_sorts() const override;
  Sort get_codomain_sort() const override;
  std::string get_uninterpreted_name() const override;
  size_t get_arity() const override;
  SortVec get_uninterpreted_param_sorts() const override;
  Datatype get_datatype() const override;
  bool compare(const Sort s) const override;
  SortKind get_sort_kind() const override;

 protected:
  sort type;
  z3::func_decl *z_func; //= func_decl(ctx);
  bool is_function;
  union zsort {
	  sort s;
	  func_decl f;
//
//	  zsort(sort a) : s(a) {};
//	  zsort(func_decl b) : f(b) {};
  };
//  union test { bool a; int b; };
//  std::variant<int, float> v, w;

  friend class Z3Solver;
};

}  // namespace smt
