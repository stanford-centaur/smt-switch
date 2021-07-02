#include "generic_datatype.h"

//#include "generic_datatype.h"
#include <memory>
#include <unordered_map>

#include "assert.h"
//#include "utils.h"

//#include "generic_datatype.h"

using namespace std;

namespace smt {

/*
GenericSort::GenericSort(SortKind sk) : sk(sk) {}

GenericSort::~GenericSort() {}

 */
/*
GenericDatatypeDecl::GenericDatatypeDecl() {}
GenericDatatypeDecl::~GenericDatatypeDecl() {}
GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl() {}
GenericDatatypeConstructorDecl::GenericDatatypeConstructorDecl() {}
GenericDatatype::GenericDatatype() {}
GenericDatatype::GenericDatatype() {}
*/

DatatypeMemoryManager::DatatypeMemoryManager()
    : name_datatypedecl_map(new unordered_map<std::string, DatatypeDecl>()),
      datatypedecl_name_map(new unordered_map<DatatypeDecl, string>()),
      name_datatypeconsdecl_map(
          new unordered_map<string, DatatypeConstructorDecl>()),
      datatypeconsdecl_name_map(
          new unordered_map<DatatypeConstructorDecl, string>()),
      dtdecl_dtconsdecl_map(
          new unordered_map<DatatypeDecl, vector<DatatypeConstructorDecl>>()),
      dtconsdecl_selector_map(new unordered_map<DatatypeConstructorDecl,
                                                vector<selectorComponents>>)
{
}

void DatatypeMemoryManager::initialize_datatype_memory()
{
  name_datatypedecl_map = unique_ptr<unordered_map<string, DatatypeDecl>>(
      new unordered_map<string, DatatypeDecl>());
  datatypedecl_name_map = unique_ptr<unordered_map<DatatypeDecl, string>>(
      new unordered_map<DatatypeDecl, string>());
}
// name_datatypedecl_map(new unordered_map<string, DatatypeDecl>());
void DatatypeMemoryManager::add_new_datatype_decl(
    const std::string & s, const DatatypeDecl & new_dt_decl)
{
  (*name_datatypedecl_map)[s] = new_dt_decl;
  (*datatypedecl_name_map)[new_dt_decl] = s;
}
string DatatypeMemoryManager::get_name_from_datatype_decl(
    const DatatypeDecl & dt)
{
  return (*datatypedecl_name_map)[dt];
}
DatatypeDecl DatatypeMemoryManager::get_datatype_decl_from_name(
    const std::string & s)
{
  return (*name_datatypedecl_map)[s];
}
void DatatypeMemoryManager::assert_dt_decl_existence(const DatatypeDecl & dt)
{
  assert(datatypedecl_name_map->find(d) != datatypedecl_name_map->end());
}
void DatatypeMemoryManager::assert_no_existence(const std::string & s)
{
  assert(name_datatypedecl_map->find(s) == name_datatypedecl_map->end());
}

void DatatypeMemoryManager::make_new_datatypecons_decl(
    const std::string & s, const DatatypeConstructorDecl & new_d_cons_decl)
{
  (*name_datatypeconsdecl_map)[s] = new_d_cons_decl;
  (*datatypeconsdecl_name_map)[new_d_cons_decl] = s;
}
DatatypeConstructorDecl DatatypeMemoryManager::get_datatypecons_decl_from_name(
    const std::string & s)
{
  return (*name_datatypeconsdecl_map)[s];
}
std::string DatatypeMemoryManager::get_name_from_datatypecons_decl(
    const DatatypeConstructorDecl & dtc)
{
  return (*datatypeconsdecl_name_map)[dtc];
}
void DatatypeMemoryManager::add_datatypecons_decl(
    const DatatypeDecl & dt, const DatatypeConstructorDecl & dtc)
{
  (*dtdecl_dtconsdecl_map)[dt].push_back(dtc);
}
std::vector<DatatypeConstructorDecl>
DatatypeMemoryManager::get_datatypecons_decl_vector(const DatatypeDecl & dt)
{
  return (*dtdecl_dtconsdecl_map)[dt];
}
shared_ptr<selectorComponents> DatatypeMemoryManager::make_selector_components(
    const std::string & name, const Sort & s)
{
  shared_ptr<selectorComponents> newSelector =
      make_shared<selectorComponents>();
  (*newSelector).name = name;
  (*newSelector).sort = s;
  return newSelector;
}

void DatatypeMemoryManager::add_selector_to_dt_cons_decl(
    const DatatypeConstructorDecl & dtc,
    const shared_ptr<selectorComponents> & newSelector)
{
  (*dtconsdecl_selector_map)[dtc].push_back(*newSelector);
}
std::vector<selectorComponents> DatatypeMemoryManager::get_selector_vector(
    const DatatypeConstructorDecl & dtc)
{
  return (*dtconsdecl_selector_map)[dtc];
}

}  // namespace smt
