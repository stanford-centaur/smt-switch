#pragma once
#include <unordered_map>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "generic_sort.h"
#include "smt_defs.h"

// using namespace smt;
namespace smt {

struct SelectorComponents
{
  std::string name;
  Sort sort;
  // Used to determine if the sort needs to be replaced later
  // on. Usually true if no further work needs to be done to the selector.
  bool finalized;
};

class GenericDatatypeDecl : public AbsDatatypeDecl
{
 public:
  GenericDatatypeDecl(const std::string name);
  virtual ~GenericDatatypeDecl(){};
  std::string get_name();

 protected:
  friend class GenericSolver;
  std::string dt_name;
};

class GenericDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  GenericDatatypeConstructorDecl(const std::string & name);
  virtual ~GenericDatatypeConstructorDecl(){};
  // Adds a new selector to the constructor object
  void add_new_selector(const SelectorComponents & newSelector);
  // Getter for the member selector_vector
  std::vector<SelectorComponents> get_selector_vector();
  std::string get_name() const;
  int get_selector_count() const;
  bool compare(const DatatypeConstructorDecl & d) const override;
  std::string get_dt_name() const;
  // Setter for the dt_decl member. Sets what datatype this
  // constructor is associated with.
  void update_stored_dt(const DatatypeDecl & datatype_decl);

 protected:
  std::vector<SelectorComponents> selector_vector;
  std::string cons_name;
  DatatypeDecl dt_decl;
  friend class GenericSolver;
  friend class GenericDatatype;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(const DatatypeDecl & dt_declaration);
  virtual ~GenericDatatype(){};
  // Stores a new constructor in the datatype object.
  void add_constructor(const DatatypeConstructorDecl & dt_cons_decl);
  // Stores a new selector in the datatype object
  void add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                    const SelectorComponents & newSelector);
  std::vector<DatatypeConstructorDecl> get_cons_vector();
  std::string get_name() const override;
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  // Updates the sort of any selector whose finalized field is false.
  void change_sort_of_selector(const Sort new_sort);
  std::hash<std::string> str_hash;

 protected:
  DatatypeDecl dt_decl;
  std::vector<DatatypeConstructorDecl> cons_decl_vector;

  friend class GenericSolver;
};

}  // namespace smt
