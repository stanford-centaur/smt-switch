#include "z3_sort.h"
#include <sstream>
#include "exceptions.h"

using namespace std;

namespace smt {

// Z3Sort implementation

std::size_t Z3Sort::hash() const {
	throw NotImplementedException("Hash not implemented for Z3 backend. ");
}

uint64_t Z3Sort::get_width() const {
//	size_t out_width;
	if (type.is_bv()) {
		return type.bv_size();
	} else {
		throw IncorrectUsageException(
				"Can only get width from bit-vector sort");
	}
}

Sort Z3Sort::get_indexsort() const {
	if (type.is_array()) {
		return std::make_shared < Z3Sort > (type.array_domain());
	} else {
		throw IncorrectUsageException(
				"Can only get width from bit-vector sort");
	}
}

Sort Z3Sort::get_elemsort() const {
	if (type.is_array()) {
		return std::make_shared < Z3Sort > (type.array_range());
	} else {
		throw IncorrectUsageException(
				"Can only get width from bit-vector sort");
	}
}

SortVec Z3Sort::get_domain_sorts() const {
	throw NotImplementedException(
			"Get_domain_sorts not implemented for Z3 backend.");
}

Sort Z3Sort::get_codomain_sort() const {
	throw NotImplementedException(
			"Get_codomain_sort not implemented for Z3 backend.");
}

string Z3Sort::get_uninterpreted_name() const {
	return type.name().str();
	throw NotImplementedException(
			"get_uninterpreted_name not implemented for Z3Sort");
}

size_t Z3Sort::get_arity() const {
	throw NotImplementedException("Get_arity not implemented for Z3 backend.");
}

SortVec Z3Sort::get_uninterpreted_param_sorts() const {
	throw NotImplementedException(
			"get_uninterpreted_param_sorts not implemented for Z3 backend.");
}

Datatype Z3Sort::get_datatype() const {
	throw NotImplementedException("get_datatype");
}
;

bool Z3Sort::compare(const Sort s) const {

	std::shared_ptr < Z3Sort > zs = std::static_pointer_cast < Z3Sort > (s);
	return true;//type == zs->type;
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
	}
//	  else if (yices_type_is_function(type))			todo: look into functions and uniterpreted
//	  {
//	    // Test if array or actually function.
//	    // This may not be the most effective way to do this.
//	    if (!is_function)
//	    {
//	      return ARRAY;
//	    }
//	    else
//	    {
//	      return FUNCTION;
//	    }
//	  }
//	  else if (yices_type_is_uninterpreted(type))
//	  {
//	    return UNINTERPRETED;
//	  }
	else {
		std::string msg("Unknown Z3 type");
//	    msg += yices_type_to_string(type, 120, 1, 0);
		throw NotImplementedException(msg.c_str());
	}
}

}  // namespace smt
