

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

class GenericDatatypeDecl : public AbsDatatypeDecl
{
 public:
  GenericDatatypeDecl(){};
  virtual ~GenericDatatypeDecl(){};

 protected:
  std::vector<DatatypeConstructorDecl> cons_decl_vector;
  friend class GenericSolver;
};

class GenericDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  GenericDatatypeConstructorDecl(const std::string & name);
  virtual ~GenericDatatypeConstructorDecl(){};
  void add_new_selector(const std::shared_ptr<selectorComponents> & newSelector);
  std::vector<selectorComponents> get_selector_vector();
  std::string get_name() const;
  int get_selector_count() const;

 protected:
  std::vector<selectorComponents> selector_vector;
  std::string cons_name;
  friend class GenericSolver;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(const DatatypeDecl & dt_declaration, const std::string & s);
  virtual ~GenericDatatype(){};
  void add_constructor(const GenericDatatypeConstructorDecl & dt_cons_decl);
  void add_selector(const GenericDatatypeConstructorDecl & dt_cons_decl, const std::shared_ptr<selectorComponents> & newSelector);
  std::vector<GenericDatatypeConstructorDecl> get_cons_vector();
  std::string get_name() const override;
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;

 protected:
  DatatypeDecl dt_decl;
  std::string name;
  std::vector<GenericDatatypeConstructorDecl> cons_decl_vector;
  
  friend class GenericSolver;
};

}  // namespace smt
