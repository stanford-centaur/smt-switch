#pragma once

#include <z3++.h>

#include <cstddef>
#include <memory>

#include "datatype.h"

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

  // declared before the symbols and sorts, so they are released while the
  // context lives
  std::shared_ptr<z3::context> c;
  std::string constructorname, datatypename;
  std::vector<z3::symbol> fieldnames{};
  std::vector<z3::sort> sorts{};
};

class Z3Datatype : public AbsDatatype
{
 public:
  Z3Datatype(const std::shared_ptr<z3::context> & ctx, z3::sort s);
  int get_num_constructors() const override;
  int get_num_selectors(std::string name) const override;
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
