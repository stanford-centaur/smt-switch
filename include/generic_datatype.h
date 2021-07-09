#pragma once
#include <unordered_map>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "sort.h"
#include "smt_defs.h"

// using namespace smt;
namespace smt {

struct SelectorComponents
{
  std::string name;
  Sort sort;
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
  void add_new_selector(
      const SelectorComponents & newSelector);
  std::vector<SelectorComponents> get_selector_vector();
  std::string get_name() const;
  int get_selector_count() const;
  bool compare(const DatatypeConstructorDecl & d) const override;

 protected:
  std::vector<SelectorComponents> selector_vector;
  std::string cons_name;
  friend class GenericSolver;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(const DatatypeDecl & dt_declaration);
  virtual ~GenericDatatype(){};
  void add_constructor(const DatatypeConstructorDecl & dt_cons_decl);
  void add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                    const SelectorComponents & newSelector);
  std::vector<DatatypeConstructorDecl> get_cons_vector();
  std::string get_name() const override;
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  //bool compare(const Datatype & d) const override;
  std::hash<std::string> str_hash;

 protected:
  DatatypeDecl dt_decl;
  std::string name;
  std::vector<DatatypeConstructorDecl> cons_decl_vector;

  friend class GenericSolver;
};

}  // namespace smt
