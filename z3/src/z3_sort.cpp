#include "z3_sort.h"
#include <sstream>
#include "exceptions.h"

using namespace std;

namespace smt {

// Z3Sort implementation

std::size_t Z3Sort::hash() const {
	if (is_function) {
		return z_func.hash();
	}
	return type.hash();
}

uint64_t Z3Sort::get_width() const {
	if (type.is_bv()) {
		return type.bv_size();
	} else {
		throw IncorrectUsageException(
				"Can only get width from bit-vector sort");
	}
}

Sort Z3Sort::get_indexsort() const {
	if (type.is_array()) {
		return std::make_shared < Z3Sort > (type.array_domain(), *ctx);
	} else {
		throw IncorrectUsageException(
				"Can only get width from bit-vector sort");
	}
}

Sort Z3Sort::get_elemsort() const {
	if (type.is_array()) {
		return std::make_shared < Z3Sort > (type.array_range(), *ctx);
	} else {
		throw IncorrectUsageException("Can only get elemsort from array sort");
	}
}

SortVec Z3Sort::get_domain_sorts() const {
	if (is_function) {
		int32_t s_arity = z_func.arity();
		SortVec sorts;
		sorts.reserve(s_arity);
		Sort s;

		for (size_t i = 0; i < s_arity; i++) {
			s.reset(new Z3Sort(z_func.domain(i), *ctx));
			sorts.push_back(s);
		}

		return sorts;
	} else {
		throw IncorrectUsageException(
				"Can only get domain sorts from function sort");
	}
}

Sort Z3Sort::get_codomain_sort() const {
	if (is_function) {
		return std::make_shared < Z3Sort > (z_func.range(), *ctx);
	} else {
		throw IncorrectUsageException(
				"Can only get codomain sort from function sort");
	}
}

string Z3Sort::get_uninterpreted_name() const {
	if (type.sort_kind() == Z3_UNINTERPRETED_SORT) {
		return type.name().str();
	} else {
		throw IncorrectUsageException(
				"Can only get uninterpreted name from uninterpreted sort");
	}
	return type.name().str();
}

size_t Z3Sort::get_arity() const {
	if (is_function) {
		return z_func.arity();
	} else {
		return 0;
	}
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const {
	throw NotImplementedException(
			"get_uninterpreted_param_sorts not implemented for Z3 backend.");
}

Datatype Z3Sort::get_datatype() const {
	throw NotImplementedException("get_datatype");
}
;

bool Z3Sort::compare(const Sort & s) const {
	std::shared_ptr<Z3Sort> zs = std::static_pointer_cast < Z3Sort > (s);
	return hash() == zs->hash();
//	if (zs->is_function) {
//		cout << "FUNCTOIN" << endl;
//		return hash() == (zs->z_func).hash()
//	}
//	return hash() == (zs->type).hash();
}

SortKind Z3Sort::get_sort_kind() const {
	if (type.is_int()) {
		return INT;
	} else if (type.is_real()) {
		return REAL;
	} else if (type.is_bool()) {
		return BOOL;
	} else if (type.is_bv()) {
		return BV;
	} else if (type.is_array()) {
		return ARRAY;
	} else if (type.is_datatype()) {
		return DATATYPE;
	} else if (type.sort_kind() == Z3_UNINTERPRETED_SORT) {
		return UNINTERPRETED;
	} else if (is_function) {
		return FUNCTION;
	} else {
		std::string msg("Unknown Z3 type");
		throw NotImplementedException(msg.c_str());
	}
}

}  // namespace smt
