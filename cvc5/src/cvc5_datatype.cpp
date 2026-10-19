#include "cvc5_datatype.h"

#include <memory>
#include <string>

#include "cvc5_sort.h"

namespace smt {

std::string Cvc5Datatype::get_constructor_name(int i) const
{
  if (i < 0 || i >= get_num_constructors())
  {
    throw IncorrectUsageException(datatype.getName() + " has no constructor "
                                  + std::to_string(i));
  }
  return datatype[i].getName();
}

std::string Cvc5Datatype::get_selector_name(std::string cons, int i) const
{
  return selector(cons, i).getName();
}

Sort Cvc5Datatype::get_selector_sort(std::string cons, int i) const
{
  return std::make_shared<Cvc5Sort>(selector(cons, i).getCodomainSort());
}

cvc5::DatatypeSelector Cvc5Datatype::selector(const std::string & cons,
                                              int i) const
{
  if (i < 0 || i >= get_num_selectors(cons))
  {
    throw IncorrectUsageException(datatype.getName() + "." + cons
                                  + " has no selector " + std::to_string(i));
  }
  return datatype.getConstructor(cons)[i];
}

bool Cvc5DatatypeConstructorDecl::compare(
    const DatatypeConstructorDecl & d) const
{
  std::shared_ptr<Cvc5DatatypeConstructorDecl> cd =
      std::static_pointer_cast<Cvc5DatatypeConstructorDecl>(d);
  return datatypeconstructordecl.toString()
         == cd->datatypeconstructordecl.toString();
}

}  // namespace smt
