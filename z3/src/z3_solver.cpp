#include "z3_solver.h"

#include <inttypes.h>

#include <iostream>

#include <z3++.h>

using namespace std;

namespace smt {

/* Z3Solver implementation */

void Z3Solver::set_opt(const std::string option, const std::string value) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::set_logic(const std::string logic) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(bool b) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Sort Z3Solver::make_sort(const DatatypeDecl &d) const {
	throw NotImplementedException("Z3Solver::make_sort");
}
;
DatatypeDecl Z3Solver::make_datatype_decl(const std::string &s) {
	throw NotImplementedException("Z3Solver::make_datatype_decl");
}
DatatypeConstructorDecl Z3Solver::make_datatype_constructor_decl(
		const std::string s) {
	throw NotImplementedException("Z3Solver::make_datatype_constructor_decl");
}
;
void Z3Solver::add_constructor(DatatypeDecl &dt,
		const DatatypeConstructorDecl &con) const {
	throw NotImplementedException("Z3Solver::add_constructor");
}
;
void Z3Solver::add_selector(DatatypeConstructorDecl &dt,
		const std::string &name, const Sort &s) const {
	throw NotImplementedException("Z3Solver::add_selector");
}
;
void Z3Solver::add_selector_self(DatatypeConstructorDecl &dt,
		const std::string &name) const {
	throw NotImplementedException("Z3Solver::add_selector_self");
}
;

Term Z3Solver::get_constructor(const Sort &s, std::string name) const {
	throw NotImplementedException("Z3Solver::get_constructor");
}
;
Term Z3Solver::get_tester(const Sort &s, std::string name) const {
	throw NotImplementedException("Z3Solver::get_testeer");
}
;

Term Z3Solver::get_selector(const Sort &s, std::string con,
		std::string name) const {
	throw NotImplementedException("Z3Solver::get_selector");
}
;

Term Z3Solver::make_term(int64_t i, const Sort &sort) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(const std::string val, const Sort &sort,
		uint64_t base) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(const Term &val, const Sort &sort) const {
	throw NotImplementedException(
			"Constant arrays not supported for Z3 backend.");
}

void Z3Solver::assert_formula(const Term &t) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Result Z3Solver::check_sat() {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Result Z3Solver::check_sat_assuming(const TermVec &assumptions) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::push(uint64_t num) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::pop(uint64_t num) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::get_value(const Term &t) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

UnorderedTermMap Z3Solver::get_array_values(const Term &arr,
		Term &out_const_base) const {
	throw NotImplementedException(
			"Z3 does not support getting array values. Please use get_value on a "
					"particular select of the array.");
}

void Z3Solver::get_unsat_core(UnorderedTermSet &out) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Sort Z3Solver::make_sort(const std::string name, uint64_t arity) const {
	z3::sort z_sort = z3::sort(ctx);

	if (!arity) {
		const char *c = name.c_str();
		z3::symbol func_name = ctx.str_symbol(c);
		z_sort = ctx.uninterpreted_sort(func_name);
	} else {
		throw NotImplementedException(
				"Z3 does not support uninterpreted type with non-zero arity.");
	}

	return std::make_shared < Z3Sort > (z_sort, ctx);
}

Sort Z3Solver::make_sort(SortKind sk) const {
	z3::sort z_sort = z3::sort(ctx);

	if (sk == BOOL) {
		z_sort = ctx.bool_sort();
	} else if (sk == INT) {
		z_sort = ctx.int_sort();
	} else if (sk == REAL) {
		z_sort = ctx.real_sort();
	} else {
		std::string msg("Can't create sort with sort constructor ");
		msg += to_string(sk);
		msg += " and no arguments";
		throw IncorrectUsageException(msg.c_str());
	}

	Sort final_sort = std::make_shared < Z3Sort > (z_sort, ctx);
	return final_sort;
}

Sort Z3Solver::make_sort(SortKind sk, uint64_t size) const {
	if (sk == BV) {
		return std::make_shared < Z3Sort > (ctx.bv_sort(size), ctx);
	} else {
		std::string msg("Can't create sort with sort constructor ");
		msg += to_string(sk);
		msg += " and an integer argument";
		throw IncorrectUsageException(msg.c_str());
	}
}

Sort Z3Solver::make_sort(SortKind sk, const Sort &sort1) const {
	throw NotImplementedException(
			"Smt-switch does not have any sorts that take one sort parameter yet.");
}

Sort Z3Solver::make_sort(SortKind sk, const Sort &sort1,
		const Sort &sort2) const {
	if (sk == ARRAY) {
		std::shared_ptr<Z3Sort> cidxsort = std::static_pointer_cast < Z3Sort
				> (sort1);
		std::shared_ptr<Z3Sort> celemsort = std::static_pointer_cast < Z3Sort
				> (sort2);
		return std::make_shared < Z3Sort
				> (ctx.array_sort(cidxsort->type, celemsort->type), ctx);
	} else {
		std::string msg("Can't create sort with sort constructor ");
		msg += to_string(sk);
		msg += " and two Sort arguments";
		throw IncorrectUsageException(msg.c_str());
	}
}

Sort Z3Solver::make_sort(SortKind sk, const Sort &sort1, const Sort &sort2,
		const Sort &sort3) const {
	throw NotImplementedException(
			"Smt-switch does not have any sorts that take three sort parameters "
					"yet.");
}

Sort Z3Solver::make_sort(SortKind sk, const SortVec &sorts) const {
	if (sk == FUNCTION) {
		if (sorts.size() < 2) {
			throw IncorrectUsageException(
					"Function sort must have >=2 sort arguments.");
		}

		// arity is one less, because last sort is return sort
		uint32_t arity = sorts.size() - 1;

		std::vector<z3::sort> zsorts;
		zsorts.reserve(arity);
		z3::sort z_sort = ctx.bool_sort();

		for (uint32_t i = 0; i < arity; i++) {
			z_sort = std::static_pointer_cast < Z3Sort > (sorts[i])->type;
			zsorts.push_back(z_sort);
		}

		Sort sort = sorts.back();
		z_sort = std::static_pointer_cast < Z3Sort > (sort)->type;

		const char *c = "throwaway name";
		z3::symbol func_name = ctx.str_symbol(c);
		z3::func_decl z_func = ctx.function(func_name, arity, &zsorts[0],
				z_sort);

		return std::make_shared < Z3Sort > (z_func, ctx);
	} else if (sorts.size() == 1) {
		return make_sort(sk, sorts[0]);
	} else if (sorts.size() == 2) {
		return make_sort(sk, sorts[0], sorts[1]);
	} else if (sorts.size() == 3) {
		return make_sort(sk, sorts[0], sorts[1], sorts[2]);
	} else {
		std::string msg("Can't create sort from sort constructor ");
		msg += to_string(sk);
		msg += " with a vector of sorts";
		throw IncorrectUsageException(msg.c_str());
	}
}

Sort Z3Solver::make_sort(const Sort &sort_con, const SortVec &sorts) const {
	throw NotImplementedException(
			"Z3 does not support uninterpreted sort constructors");
}

Term Z3Solver::make_symbol(const std::string name, const Sort &sort) {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_param(const std::string name, const Sort &sort) {
	throw NotImplementedException("make_param not supported by Z3 yet.");
}

Term Z3Solver::make_term(Op op, const Term &t) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(Op op, const Term &t0, const Term &t1) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(Op op, const Term &t0, const Term &t1,
		const Term &t2) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::make_term(Op op, const TermVec &terms) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::reset() {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::reset_assertions() {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

Term Z3Solver::substitute(const Term term,
		const UnorderedTermMap &substitution_map) const {
	throw NotImplementedException(
			"Term iteration not implemented for Z3 backend.");
}

void Z3Solver::dump_smt2(std::string filename) const {
	throw NotImplementedException("Dumping smt2 not supported by Z3 backend.");
}

/* end Z3Solver implementation */

}  // namespace smt
