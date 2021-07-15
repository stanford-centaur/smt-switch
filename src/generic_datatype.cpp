#include "generic_datatype.h"

#include <algorithm>
#include <exception>
#include <memory>
#include <unordered_map>

#include "assert.h"

using namespace std;

namespace smt {

GenericDatatypeDecl::GenericDatatypeDecl(const std::string name) : dt_name(name)
{
}

std::string GenericDatatypeDecl::get_name() { return dt_name; }

GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl(
    const std::string & name)
  : cons_name(name)
{
}

void GenericDatatypeConstructorDecl::add_new_selector(
    const SelectorComponents & newSelector)
{
  for (unsigned int i = 0; i < selector_vector.size(); ++i)
  {
    if (selector_vector[i].name == (newSelector).name)
    {
      throw "Can't add selector. It already exists in this datatype!";
    }
  }
  selector_vector.push_back(newSelector);
}

std::vector<SelectorComponents>
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
  return cons_name
         == static_pointer_cast<GenericDatatypeConstructorDecl>(d)->get_name();
}

  std::string GenericDatatypeConstructorDecl::get_dt_name() const
  {
    return static_pointer_cast<GenericDatatypeDecl>(dt_decl)->get_name();
  }

  void GenericDatatypeConstructorDecl::update_stored_dt(const DatatypeDecl & datatype_decl)
  {
    dt_decl = datatype_decl;
    
  }

GenericDatatype::GenericDatatype(const DatatypeDecl & dt_declaration)
    : dt_decl(dt_declaration)
{
}

void GenericDatatype::add_constructor(
    const DatatypeConstructorDecl & dt_cons_decl)
{
  if (std::find(cons_decl_vector.begin(), cons_decl_vector.end(), dt_cons_decl)
      != cons_decl_vector.end())
  {
    throw "Can't add constructor. It already has been added!";
  }
  shared_ptr<GenericDatatypeConstructorDecl> gdt_cons = static_pointer_cast<GenericDatatypeConstructorDecl>(dt_cons_decl);
  gdt_cons->update_stored_dt(dt_decl);
  cons_decl_vector.push_back(dt_cons_decl);
}

void GenericDatatype::add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                                   const SelectorComponents & newSelector)
{
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  {
    if (cons_decl_vector[i] == dt_cons_decl)
    {
      static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i])
          ->add_new_selector(newSelector);
    }
  }
}
std::vector<DatatypeConstructorDecl> GenericDatatype::get_cons_vector()
{
  return cons_decl_vector;
}

std::string GenericDatatype::get_name() const
{
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
    if (static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i])
            ->get_name()
        == cons)
    {
      num_selectors = static_pointer_cast<GenericDatatypeConstructorDecl>(
                          cons_decl_vector[i])
                          ->get_selector_count();
    }
  }
  return num_selectors;
}

  void GenericDatatype::change_sort_of_selector(const Sort new_sort)
  {
    for (unsigned int i = 0; i < cons_decl_vector.size(); ++i) {
      std::shared_ptr<GenericDatatypeConstructorDecl> cons_cast = static_pointer_cast<GenericDatatypeConstructorDecl>(cons_decl_vector[i]);
      for (unsigned int f = 0; f < get_num_selectors(cons_cast->get_name()); ++f) {
	
	if (cons_cast->selector_vector[f].finalized == false) {
	  cons_cast->selector_vector[f].sort = new_sort;
	  cons_cast->selector_vector[f].finalized = true;
	}
      }
    
    }
  }
  
}  // namespace smt
