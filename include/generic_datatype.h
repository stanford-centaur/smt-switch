
#pragma once

#include <functional>

#include "datatype.h"
#include "exceptions.h"
#include "smt_defs.h"
#include "sort.h"

// using namespace smt;
namespace smt {

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
  GenericDatatypeConstructorDecl(){};
  virtual ~GenericDatatypeConstructorDecl(){};

 protected:
  friend class GenericSolver;
};

class GenericDatatype : public AbsDatatype
{
 public:
  GenericDatatype(){};
  virtual ~GenericDatatype(){};

 protected:
  friend class GenericSolver;
};
