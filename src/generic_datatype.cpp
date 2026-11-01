#include "generic_datatype.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <memory>
#include <string>
#include <tuple>
#include <utility>

#include "exceptions.h"
#include "sort.h"
#include "utils.h"

namespace smt {

GenericDatatypeDecl::GenericDatatypeDecl(std::string name)
    : dt_name(std::move(name))
{
}

std::string GenericDatatypeDecl::get_name() const { return dt_name; }

GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl(
    const std::string & name)
    : cons_name(name)
{
}

std::string GenericDatatypeConstructorDecl::get_name() const
{
  return cons_name;
}

// A selector of a declaration compares by its name and sort. A self
// selector's sort is null there, as make_sort gives the datatype's sort only
// to the copy the datatype sort keeps, so it never changes once added.
static bool selector_equal(const SelectorComponents & a,
                           const SelectorComponents & b)
{
  return std::tie(a.name, a.sort) == std::tie(b.name, b.sort);
}

static bool selector_less(const SelectorComponents & a,
                          const SelectorComponents & b)
{
  return std::tie(a.name, a.sort) < std::tie(b.name, b.sort);
}

std::size_t GenericDatatypeConstructorDecl::hash() const
{
  // The name and each selector's name and sort, as compare checks them.
  std::size_t h = std::hash<std::string>{}(cons_name);
  for (const SelectorComponents & sel : selector_vector)
  {
    detail::hash_combine(h, sel.name);
    detail::hash_combine(h, sel.sort);
  }
  return h;
}

bool GenericDatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  auto other = std::dynamic_pointer_cast<GenericDatatypeConstructorDecl>(d);
  return other && cons_name == other->cons_name
         && std::equal(selector_vector.begin(),
                       selector_vector.end(),
                       other->selector_vector.begin(),
                       other->selector_vector.end(),
                       selector_equal);
}

bool GenericDatatypeConstructorDecl::less(
    const DatatypeConstructorDecl & d) const
{
  auto other = backend_pointer_cast<GenericDatatypeConstructorDecl>(d);
  if (cons_name != other->cons_name)
  {
    return cons_name < other->cons_name;
  }
  return std::lexicographical_compare(selector_vector.begin(),
                                      selector_vector.end(),
                                      other->selector_vector.begin(),
                                      other->selector_vector.end(),
                                      selector_less);
}

void GenericDatatypeConstructorDecl::add_new_selector(
    const SelectorComponents & newSelector)
{
  for (unsigned int i = 0; i < selector_vector.size(); ++i)
  {
    // Checks if the selector has already been added
    if (selector_vector[i].name == (newSelector).name)
    {
      throw InternalSolverException(
          "Can't add selector. It already exists in this datatype!");
    }
  }
  selector_vector.push_back(newSelector);
}

std::vector<SelectorComponents>
GenericDatatypeConstructorDecl::get_selector_vector() const
{
  return selector_vector;
}

int GenericDatatypeConstructorDecl::get_selector_count() const
{
  return selector_vector.size();
}

std::string GenericDatatypeConstructorDecl::get_dt_name() const
{
  return dt_decl->get_name();
}

void GenericDatatypeConstructorDecl::update_stored_dt(
    const DatatypeDecl & datatype_decl)
{
  dt_decl = datatype_decl;
}

GenericDatatype::GenericDatatype(const DatatypeDecl & dt_declaration)
    : dt_decl(dt_declaration)
{
}

int GenericDatatype::get_num_constructors() const
{
  return cons_decl_vector.size();
}

int GenericDatatype::get_num_selectors(std::string cons) const
{
  // Used to keep track of the number of selectors in the constructor
  int num_selectors = 0;
  bool found = false;
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  // Searches for a matching constructor
  {
    if (std::static_pointer_cast<GenericDatatypeConstructorDecl>(
            cons_decl_vector[i])
            ->get_name()
        == cons)
    {
      found = true;
      // Calls the constructor's get_selector_count() function
      num_selectors = std::static_pointer_cast<GenericDatatypeConstructorDecl>(
                          cons_decl_vector[i])
                          ->get_selector_count();
      break;
    }
  }
  if (!found)
  {
    throw IncorrectUsageException("Constructor not found");
  }
  return num_selectors;
}

std::vector<std::string> GenericDatatype::get_constructor_names() const
{
  std::vector<std::string> names;
  for (const DatatypeConstructorDecl & con : cons_decl_vector)
  {
    names.push_back(con->get_name());
  }
  return names;
}

std::vector<std::string> GenericDatatype::get_selector_names(
    const std::string & cons) const
{
  for (const DatatypeConstructorDecl & con : cons_decl_vector)
  {
    if (con->get_name() == cons)
    {
      std::vector<std::string> names;
      for (const SelectorComponents & sel :
           std::static_pointer_cast<GenericDatatypeConstructorDecl>(con)
               ->get_selector_vector())
      {
        names.push_back(sel.name);
      }
      return names;
    }
  }
  throw IncorrectUsageException("Constructor not found");
}

Sort GenericDatatype::get_selector_sort(const std::string & cons,
                                        const std::string & sel) const
{
  for (const DatatypeConstructorDecl & con : cons_decl_vector)
  {
    if (con->get_name() != cons)
    {
      continue;
    }
    for (const SelectorComponents & selector :
         std::static_pointer_cast<GenericDatatypeConstructorDecl>(con)
             ->get_selector_vector())
    {
      if (selector.name == sel)
      {
        return selector.sort;
      }
    }
    throw IncorrectUsageException("Selector not found");
  }
  throw IncorrectUsageException("Constructor not found");
}

std::string GenericDatatype::get_name() const { return dt_decl->get_name(); }

void GenericDatatype::add_constructor(
    const DatatypeConstructorDecl & dt_cons_decl)
{
  // Constructor names are unique within a datatype, and two declarations of
  // one name can differ in their selectors, so the names are compared.
  if (std::any_of(cons_decl_vector.begin(),
                  cons_decl_vector.end(),
                  [&dt_cons_decl](const DatatypeConstructorDecl & c) {
                    return c->get_name() == dt_cons_decl->get_name();
                  }))
  {
    throw InternalSolverException(
        "Can't add constructor. It already has been added!");
  }
  std::shared_ptr<GenericDatatypeConstructorDecl> gdt_cons =
      backend_pointer_cast<GenericDatatypeConstructorDecl>(dt_cons_decl);
  // Links the constructor to the datatype_decl of the datatype
  gdt_cons->update_stored_dt(dt_decl);
  // Links the datatype to the new constructor
  cons_decl_vector.push_back(dt_cons_decl);
}

void GenericDatatype::add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                                   const SelectorComponents & newSelector)
{
  // Boolean used to keep track of if a successful match was found.
  bool success = false;
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  {
    // If the constructor is associated with the datatype
    if (cons_decl_vector[i] == dt_cons_decl)
    {
      // Adds the selector to the correct constructor
      std::static_pointer_cast<GenericDatatypeConstructorDecl>(
          cons_decl_vector[i])
          ->add_new_selector(newSelector);
      success = true;
      break;
    }
  }
  if (!success)
  {
    throw InternalSolverException(
        "Can't add selector. The constructor is not a member of the datatype!");
  }
}

std::vector<DatatypeConstructorDecl> GenericDatatype::get_cons_vector() const
{
  return cons_decl_vector;
}

/*
This function goes through every selector in the datatype and if
finalized is set to false, it replaces the previously stored sort
with new_sort
 */
void GenericDatatype::change_sort_of_selector(const Sort new_sort)
{
  // For every constructor
  for (unsigned int i = 0; i < cons_decl_vector.size(); ++i)
  {
    std::shared_ptr<GenericDatatypeConstructorDecl> cons_cast =
        std::static_pointer_cast<GenericDatatypeConstructorDecl>(
            cons_decl_vector[i]);
    // For every selector
    for (int f = 0; f < get_num_selectors(cons_cast->get_name()); ++f)
    {
      if (cons_cast->selector_vector[f].finalized == false)
      {
        // Updates the selector's members
        cons_cast->selector_vector[f].sort = new_sort;
        cons_cast->selector_vector[f].finalized = true;
      }
    }
  }
}

}  // namespace smt
