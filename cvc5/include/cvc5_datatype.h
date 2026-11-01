
/*********************                                                        */
/*! \file cvc5_datatype.h
** \verbatim
** Top contributors (to current version):
**   Kristopher Brown
** This file is part of the smt-switch project.
** Copyright (c) 2020 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Thin wrapper for cvc5 Datatype-related classes.
**/

#pragma once

#include <cvc5/cvc5.h>

#include <cstddef>
#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "datatype.h"
#include "smt_defs.h"

namespace smt {

class Cvc5DatatypeConstructorDecl : public AbsDatatypeConstructorDecl
{
 public:
  Cvc5DatatypeConstructorDecl(cvc5::DatatypeConstructorDecl t, std::string n);
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const DatatypeConstructorDecl &) const override;
  bool less(const DatatypeConstructorDecl & d) const override;

 protected:
  cvc5::DatatypeConstructorDecl datatypeconstructordecl;
  // cvc5's declaration cannot be asked for its name
  std::string name;
  // nor for its selectors; a null sort stands for one added with
  // add_selector_self
  std::vector<std::pair<std::string, cvc5::Sort>> selectors;

  friend class Cvc5Solver;
};

class Cvc5DatatypeDecl : public AbsDatatypeDecl
{
 public:
  explicit Cvc5DatatypeDecl(cvc5::DatatypeDecl t);
  std::string get_name() const override;

 protected:
  cvc5::DatatypeDecl datatypedecl;
  // the constructors added, from which make_sort builds a fresh cvc5
  // declaration: one cvc5 resolves shares its constructors' declarations,
  // so a selector added to one later would reach the datatype
  std::vector<std::shared_ptr<Cvc5DatatypeConstructorDecl>> constructors;
  // whether it was used for a sort, which a fresh declaration does not
  // record
  bool used = false;

  friend class Cvc5Solver;
};

class Cvc5Datatype : public AbsDatatype
{
 public:
  explicit Cvc5Datatype(cvc5::Datatype t);
  int get_num_constructors() const override;
  int get_num_selectors(std::string cons) const override;
  std::vector<std::string> get_constructor_names() const override;
  std::vector<std::string> get_selector_names(
      const std::string & cons) const override;
  Sort get_selector_sort(const std::string & cons,
                         const std::string & sel) const override;
  std::string get_name() const override;
  std::size_t hash() const override;
  bool compare(const Datatype & d) const override;
  bool less(const Datatype & d) const override;

 protected:
  cvc5::Datatype datatype;

  friend class Cvc5Solver;
};

}  // namespace smt
