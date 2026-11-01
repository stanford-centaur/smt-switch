#pragma once

#include <z3++.h>

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "datatype.h"
#include "smt_defs.h"

namespace smt {

class Z3DatatypeDecl : public AbsDatatypeDecl
{
 public:
  explicit Z3DatatypeDecl(std::string n);
  std::string get_name() const override;

 protected:
  friend class Z3Solver;
  std::string name;
  std::vector<DatatypeConstructorDecl> consvec{};
  // whether it was used for a sort; Z3 would give the same sort back for
  // the name, however the constructors changed
  bool used = false;
};

class Z3DatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  Z3DatatypeConstructorDecl(const std::shared_ptr<z3::context> & ctx,
                            std::string name);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl &) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

 protected:
  friend class Z3Solver;

  // declared before the sorts, so they are released while the context lives
  std::shared_ptr<z3::context> c;
  std::string constructorname, datatypename;
  // the selectors added; a null sort stands for one added with
  // add_selector_self
  std::vector<std::pair<std::string, z3::sort>> selectors{};
};

class Z3Datatype : public AbsDatatype
{
 public:
  Z3Datatype(const std::shared_ptr<z3::context> & ctx, z3::sort s);
  int get_num_constructors() const override;
  int get_num_selectors(std::string name) const override;
  std::vector<std::string> get_constructor_names() const override;
  std::vector<std::string> get_selector_names(
      const std::string & cons) const override;
  Sort get_selector_sort(const std::string & cons,
                         const std::string & sel) const override;
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const Datatype & d) const override;
  bool less(const Datatype & d) const override;

 private:
  // declared before datatype, so that it is released while the context lives
  std::shared_ptr<z3::context> c;

  z3::sort datatype;
  friend class Z3Solver;
};

}  // namespace smt
