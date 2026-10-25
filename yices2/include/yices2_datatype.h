/*!
 * \file yices2_datatype.h
 * \brief Yices2 implementation of the datatype interfaces, for enumerations.
 * \author Po-Chun Chien
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 *
 * Yices2 has no algebraic datatypes, but a scalar type is an enumeration:
 * a finite type whose distinct constants are all of its values. So a
 * datatype whose constructors have no selectors becomes a scalar type named
 * after it, with the i-th constructor's name on the i-th constant. Yices
 * keeps both names, so the type alone gives back the whole datatype.
 */

#pragma once

#include <yices.h>

#include <cstddef>
#include <string>
#include <vector>

#include "datatype.h"
#include "smt_defs.h"
#include "yices2_instance_ref.h"

namespace smt {

class Yices2DatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  explicit Yices2DatatypeConstructorDecl(std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl & d) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

 protected:
  std::string name;

  friend class Yices2Solver;
};

class Yices2DatatypeDecl : public AbsDatatypeDecl
{
 public:
  explicit Yices2DatatypeDecl(std::string n);
  std::string get_name() const override;

 protected:
  std::string name;
  std::vector<std::string> constructors;  ///< their names, in order

  friend class Yices2Solver;
};

class Yices2Datatype : public AbsDatatype
{
 public:
  explicit Yices2Datatype(type_t t);
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const Datatype & d) const override;
  bool less(const Datatype & d) const override;

  /** The constant the constructor `cons` stands for, or NULL_TERM if the
   *  datatype has no constructor of that name */
  term_t get_constant(const std::string & cons) const;

 protected:
  // keeps Yices set up while the datatype can be used, even past its solver
  Yices2InstanceRef instance;
  type_t type;  ///< a scalar type
};

}  // namespace smt
