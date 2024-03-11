#pragma once
#include <memory>
#include <string>
#include <vector>

#include "datatype.h"
#include "exceptions.h"
#include "z3++.h"

namespace smt {

// forward declaration
class Z3Solver;
class z3Datatype;
class z3DatatypeConstructorDecl;
class z3DatatypeDecl : public AbsDatatypeDecl
{
 public:
  z3DatatypeDecl(z3::context & c, std::string name) : c(c), name(name){};

 protected:
  friend class Z3Solver;
  friend class z3Datatype;
  z3::context & c;
  std::string name;
  std::vector<DatatypeConstructorDecl> consvec {};
};

class z3DatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  z3DatatypeConstructorDecl(z3::context & c, std::string name)
      : c(c), name(name){};
  bool compare(const DatatypeConstructorDecl &) const override;

 private:
  void addField(std::string fn, const Sort & sort);
  void addSelfRef(std::string name);

 protected:
  friend class Z3Solver;
  friend class z3Datatype;

  z3::context & c;
  std::string name;
  std::vector<std::string> names {};
  std::vector<Sort> sorts {};
};

class z3Datatype : public AbsDatatype
{
 public:
  z3Datatype(z3::context & c, z3::sort s) : c(c), datatype(s) {}
  std::string get_name() const override { return datatype.name().str(); }
  int get_num_constructors() const override
  {
    return Z3_get_datatype_sort_num_constructors(c, datatype);
  }
  int get_num_selectors(std::string name) const override
  {
    for (size_t i = 0; i < get_num_constructors(); i++)
    {
      z3::func_decl cons{ c, Z3_get_datatype_sort_constructor(c, datatype, i) };
      if (cons.name().str() == name) return cons.num_parameters();
    }
    throw InternalSolverException(datatype.name().str() + "." + name
                                  + " not found");
  }

 private:
  z3::context & c;

  z3::sort datatype;
  friend class Z3Solver;
};

}  // namespace smt
