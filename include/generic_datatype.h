#pragma once
#include <unordered_map>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "generic_sort.h"
#include "smt_defs.h"

namespace smt {

// Struct used to hold everything needed to work with datatype selectors
struct SelectorComponents
{
  // Name of the selector and its associated sort
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
  std::string get_name() const;
  int get_param_count() const;
  std::vector<Sort> get_param_sorts();
  void register_param_sort(std::string param_name);

 protected:
  friend class GenericSolver;
  std::string dt_name;
  int param_count;
  std::vector<Sort> param_sorts;
  
};

class GenericDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  GenericDatatypeConstructorDecl(const std::string & name);
  virtual ~GenericDatatypeConstructorDecl(){};
  // Stores a new selector in the constructor object. newSelector: the
  // SelectorComponents to be added.
  void add_new_selector(const SelectorComponents & newSelector);
  std::vector<SelectorComponents> get_selector_vector();
  std::string get_name() const;
  // Returns the size of selector_vector
  int get_selector_count() const;
  bool compare(const DatatypeConstructorDecl & d) const override;
  std::string get_dt_name() const;
  void add_selector_param(const std::string & name, int param_num);

 protected:
  std::vector<SelectorComponents> selector_vector;
  std::string cons_name;
  bool contains_param;

  DatatypeDecl dt_decl;
  // Setter for the dt_decl member. Only to be used when a constructor
  // is added to a datatype. datatype_decl: The DatatypeDecl of the datatype.
  void update_stored_dt(const DatatypeDecl & datatype_decl);
  friend class GenericSolver;
  friend class GenericDatatype;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(const DatatypeDecl & dt_declaration);
  virtual ~GenericDatatype(){};
  // Stores a constructor object (dt_cons_decl) in the datatype object.
  void add_constructor(const DatatypeConstructorDecl & dt_cons_decl);
  // Stores a new selector (newSelector) in the constructor object
  // (dt_cons_decl) if the constructor is associated with the datatype
  void add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                    const SelectorComponents & newSelector);
  std::vector<DatatypeConstructorDecl> get_cons_vector();
  std::string get_name() const override;
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  // Updates the sort of any selector whose finalized field is
  // false. The not-finalized selectors have their sorts set to new_sort.
  // This function is used only as part of the process of adding a
  // 'self-selector'. After a self selector is added to a datatype, it
  // holds a placeholder sort. This function is
  // called when the datatype's sort is created to replace the
  // self-selector's placeholder sort with the actual datatype sort.
  void change_sort_of_selector(const Sort new_sort);
  std::hash<std::string> str_hash;

 protected:
  DatatypeDecl dt_decl;

  std::vector<DatatypeConstructorDecl> cons_decl_vector;

  friend class GenericSolver;
};

}  // namespace smt
