#include "generic_datatype.h"

#include <memory>
#include <unordered_map>
#include <exception>
#include "assert.h"
#include <algorithm>

using namespace std;

namespace smt {

GenericDatatypeDecl::GenericDatatypeDecl(const std::string name) :dt_name(name)
{
}

std::string GenericDatatypeDecl::get_name()
{
  return dt_name;
}
  
GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl(
    const std::string & name)
    : cons_name(name)
{
}

void GenericDatatypeConstructorDecl::add_new_selector(
    const shared_ptr<selectorComponents> & newSelector)
{
  // This seems like an opportunity for a new comparison function for
  // the struct.
  for (unsigned int i = 0; i < selector_vector.size(); ++i) {
    if (selector_vector[i].name == (*newSelector).name) {
      throw "Can't add selector. It already exists in vector!";
    }
  }
  selector_vector.push_back(*newSelector);
}

std::vector<selectorComponents>
GenericDatatypeConstructorDecl::get_selector_vector()
{
  return selector_vector;
}

std::string GenericDatatypeConstructorDecl::get_name() const
{
  return cons_name;
}

int GenericDatatypeConstructorDecl::get_selector_count() const
{
  return selector_vector.size();
}
bool GenericDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  // Why won't type casting like this work?
  // GenericDatatypeConstructorDecl gdtc = (GenericDatatypeConstructorDecl) d;
  return cons_name == static_pointer_cast<GenericDatatypeConstructorDecl>(d)->get_name();
}

GenericDatatype::GenericDatatype(const DatatypeDecl & dt_declaration)
    : dt_decl(dt_declaration)
{
}

void GenericDatatype::add_constructor(
    const DatatypeConstructorDecl & dt_cons_decl)
{
  if (std::find(cons_decl_vector.begin(), cons_decl_vector.end(), dt_cons_decl) != cons_decl_vector.end()) {
    throw "Can't add constructor. It already has been added!";
  }
  cons_decl_vector.push_back(dt_cons_decl);
}

void GenericDatatype::add_selector(
    const DatatypeConstructorDecl & dt_cons_decl,
    const std::shared_ptr<selectorComponents> & newSelector)
{
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  {
    if (cons_decl_vector[i] == dt_cons_decl)
    {
      static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i])->add_new_selector(newSelector);
    }
  }
}
std::vector<DatatypeConstructorDecl> GenericDatatype::get_cons_vector()
{
  return cons_decl_vector;
}

  std::string GenericDatatype::get_name() const {
    return static_pointer_cast<GenericDatatypeDecl>(dt_decl)->get_name();
}

int GenericDatatype::get_num_constructors() const
{
  return cons_decl_vector.size();
}

int GenericDatatype::get_num_selectors(std::string cons) const
{
  int num_selectors = 0;
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  {
    if (static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i])->get_name() == cons)
    {
      num_selectors = static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i])->get_selector_count();
    }
  }
  return num_selectors;
}
  // Still deciding if I should implement a datatype comparison function
  /*
bool GenericDatatype::compare(const Datatype & d) const
{
  return name == d->get_name();
}
  */

}  // namespace smt
