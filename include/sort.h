#ifndef SMT_SORT_H
#define SMT_SORT_H

#include <array>
#include <memory>
#include <string>

// Sort needs to have arguments
//  could be integers or other sorts
//  should use an enum for the different types of sorts probably

namespace smt
{
  // TODO : add other smt types
  enum Type
  {
   ARRAY=0,
   BV,
   INT,
   REAL,
   UNINTERPRETED,
   /** IMPORTANT: This must stay at the bottom.
      It's only use is for sizing the type2str array */
   NUM_TYPES
  };

  /**
     Base class for representing an SMT sort.
     It holds a type enum and any necessary data for that particular sort.

     Sort objects should never be constructed directly, but instead provided
     by a Solver.
   */
  class Sort
  {
  public:
    Sort(Type t) : type(t), identifier("BaseClassSort") {};
    ~Sort() = default;
    std::string to_string() { return identifier; };
    virtual bool is_array() const { return false; };
    virtual bool is_bv() const { return false; };
    virtual bool is_int() const { return false; };
    virtual bool is_real() const { return false; };
    // TODO: decide on exception or special value for incorrect usage
    virtual unsigned int get_width() const { return 0; };
  protected:
    std::string identifier;
    Type type;
  };

  class ArraySort : public Sort
  {
  public:
    ArraySort(Sort isort, Sort esort) : Sort(ARRAY), indexsort(isort), elemsort(esort) {} ;
    bool is_array() const override { return true; };
  private:
    Sort indexsort;
    Sort elemsort;
  };

  class BVSort : public Sort
  {
  public:
    BVSort(unsigned int w) : Sort(BV), width(w)
    {
      identifier = "BV(" + std::to_string(w) + ")";
    }
    // overload bv-specific methods
    bool is_bv() const override { return true; };
    unsigned int get_width() const override { return width; };
  private:
    unsigned int width;
  };

  class IntSort : public Sort
  {
  public:
    IntSort() : Sort(INT) {};
    bool is_int() const override { return true; };
  };

  class RealSort : public Sort
  {
  public:
    RealSort() : Sort(REAL) {};
    bool is_real() const override { return true; };
  };


  /**
     This function should only be called once, to generate the constexpr
     type2str for converting enums to string_views.
   */
  constexpr std::array<std::string_view, NUM_TYPES> generate_type2str()
  {
    std::array<std::string_view, NUM_TYPES> type2str;
    type2str[ARRAY] = std::string_view("Array");
    type2str[BV] = std::string_view("BV");
    type2str[INT] = std::string_view("INT");
    type2str[REAL] = std::string_view("REAL");
    type2str[UNINTERPRETED] = std::string_view("UNINTERPRETED");
    return type2str;
  }

  constexpr std::array<std::string_view, NUM_TYPES> type2str = generate_type2str();

}

#endif
