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

class Z3Sort: public AbsSort {
public:
	// Non-functions
	Z3Sort(sort z3sort, context &c) :
			type(z3sort), is_function(false), z_func(c) {
		ctx = &c;
	}
	;

	// Functions
	Z3Sort(func_decl zfunc, context &c) :
			type(c), is_function(true), z_func(zfunc) {
	}
	;

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
	func_decl z_func;
	bool is_function;
	context *ctx;

	friend class Z3Solver;
};

}  // namespace smt
