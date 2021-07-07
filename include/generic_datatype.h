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
  friend class GenericSolver;
};

class GenericDatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  GenericDatatypeConstructorDecl(const std::string & name);
  virtual ~GenericDatatypeConstructorDecl(){};
  void add_new_selector(
      const std::shared_ptr<selectorComponents> & newSelector);
  std::vector<selectorComponents> get_selector_vector();
  std::string get_name() const;
  int get_selector_count() const;
  bool compare(const DatatypeConstructorDecl & d) const override;

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
  void add_constructor(const DatatypeConstructorDecl & dt_cons_decl);
  void add_selector(const DatatypeConstructorDecl & dt_cons_decl,
                    const std::shared_ptr<selectorComponents> & newSelector);
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
