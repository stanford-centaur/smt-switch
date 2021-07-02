
//#pragma once

//#include <functional>

#include <unordered_map>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "generic_sort.h"
#include "smt_defs.h"

// using namespace smt;
namespace smt {

struct selectorComponents
{
  std::string name;
  Sort sort;
};

class DatatypeMemoryManager
{
 public:
  DatatypeMemoryManager();
  virtual ~DatatypeMemoryManager(){};
  void initialize_datatype_memory();
  void add_new_datatype_decl(const std::string & s,
                             const DatatypeDecl & new_dt_decl);
  DatatypeDecl get_datatype_decl_from_name(const std::string & s);
  std::string get_name_from_datatype_decl(const DatatypeDecl & new_dt_decl);
  void assert_dt_decl_existence(const DatatypeDecl & dt);
  void assert_no_existence(const std::string & s);
  void make_new_datatypecons_decl(
      const std::string & s, const DatatypeConstructorDecl & new_d_cons_decl);
  DatatypeConstructorDecl get_datatypecons_decl_from_name(
      const std::string & s);
  std::string get_name_from_datatypecons_decl(
      const DatatypeConstructorDecl & dtc);
  void add_datatypecons_decl(const DatatypeDecl & dt,
                             const DatatypeConstructorDecl & dtc);
  std::vector<DatatypeConstructorDecl> get_datatypecons_decl_vector(
      const DatatypeDecl & dt);

  std::shared_ptr<selectorComponents> make_selector_components(
      const std::string & name, const Sort & s);
  void add_selector_to_dt_cons_decl(
      const DatatypeConstructorDecl & dtc,
      const std::shared_ptr<selectorComponents> & newSelector);
  std::vector<selectorComponents> get_selector_vector(
      const DatatypeConstructorDecl & dtc);

 private:
  std::unique_ptr<std::unordered_map<std::string, DatatypeDecl>>
      name_datatypedecl_map;
  std::unique_ptr<std::unordered_map<DatatypeDecl, std::string>>
      datatypedecl_name_map;
  std::unique_ptr<std::unordered_map<std::string, DatatypeConstructorDecl>>
      name_datatypeconsdecl_map;
  std::unique_ptr<std::unordered_map<DatatypeConstructorDecl, std::string>>
      datatypeconsdecl_name_map;
  std::unique_ptr<
      std::unordered_map<DatatypeDecl, std::vector<DatatypeConstructorDecl>>>
      dtdecl_dtconsdecl_map;

  std::unique_ptr<std::unordered_map<DatatypeConstructorDecl,
                                     std::vector<selectorComponents>>>
      dtconsdecl_selector_map;

 protected:
  friend class GenericSolver;
};

class GenericDatatypeDecl : public AbsDatatypeDecl
{
 public:
  GenericDatatypeDecl(){};
  virtual ~GenericDatatypeDecl(){};

 protected:
  friend class GenericSolver;
};

class GenericDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  GenericDatatypeConstructorDecl(){};
  virtual ~GenericDatatypeConstructorDecl(){};

 protected:
  friend class GenericSolver;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(){};
  virtual ~GenericDatatype(){};

 protected:
  friend class GenericSolver;
};

}  // namespace smt
