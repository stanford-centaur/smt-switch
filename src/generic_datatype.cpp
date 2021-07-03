#include "generic_datatype.h"

#include <memory>
#include <unordered_map>

#include "assert.h"


using namespace std;

namespace smt {


  GenericDatatype::GenericDatatype(const DatatypeDecl & dt_declaration, const std::string & s) : dt_decl(dt_declaration), name(s) {
  }

  GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl(const std::string & name) : cons_name(name) {}
  void GenericDatatypeConstructorDecl::add_new_selector(const shared_ptr<selectorComponents> & newSelector)
  {
    selector_vector.push_back(*newSelector);
  }


  std::vector<selectorComponents> GenericDatatypeConstructorDecl::get_selector_vector()
  {
    return selector_vector;
  }

  void GenericDatatype::add_constructor(const GenericDatatypeConstructorDecl & dt_cons_decl)
  {
    cons_decl_vector.push_back(dt_cons_decl);
  }

  std::string GenericDatatype::get_name() const
  {
    return name;
  }

  int GenericDatatypeConstructorDecl::get_selector_count() const
  {
    return selector_vector.size();
  }

  int GenericDatatype::get_num_constructors() const
  {
    return cons_decl_vector.size();
  }

  int GenericDatatype::get_num_selectors(std::string cons) const
  {
    int num_selectors = 0;
    for (unsigned int i = 0; i < cons_decl_vector.size(); ++i) {
      if (cons_decl_vector[i].get_name() == cons) {
        num_selectors = cons_decl_vector[i].get_selector_count();
      }
    }
    return num_selectors;
  }
  
  void GenericDatatype::add_selector(const GenericDatatypeConstructorDecl & dt_cons_decl, const std::shared_ptr<selectorComponents> & newSelector)
  {
    for (unsigned int i = 0; i < cons_decl_vector.size(); ++i) {
      if (cons_decl_vector[i].get_name() == dt_cons_decl.get_name()) {
	cons_decl_vector[i].get_selector_vector().push_back(*newSelector);
      }
    }
  }
  std::vector<GenericDatatypeConstructorDecl> GenericDatatype::get_cons_vector()
  {
    return cons_decl_vector;
  }

  std::string GenericDatatypeConstructorDecl::get_name() const
  {
    return cons_name;
  }

}  // namespace smt
