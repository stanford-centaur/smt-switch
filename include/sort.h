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
   BOOL,
   BV,
   INT,
   REAL,
   UNINTERPRETED,
   /** IMPORTANT: This must stay at the bottom.
                  It's only use is for sizing the type2str array
   */
   NUM_TYPES
  };

  /**
     This function should only be called once, to generate the constexpr
     type2str for converting enums to string_views.
  */
  constexpr std::array<std::string_view, NUM_TYPES> generate_type2str()
    {
      std::array<std::string_view, NUM_TYPES> type2str;
      type2str[ARRAY] = std::string_view("ARRAY");
      type2str[BOOL] = std::string_view("BOOL");
      type2str[BV] = std::string_view("BV");
      type2str[INT] = std::string_view("INT");
      type2str[REAL] = std::string_view("REAL");
      type2str[UNINTERPRETED] = std::string_view("UNINTERPRETED");
      return type2str;
    }

  constexpr std::array<std::string_view, NUM_TYPES> type2str = generate_type2str();

  /**
     Abstract base class for representing an SMT sort.
     It holds a type enum and any necessary data for that particular sort.

     Sort objects should never be constructed directly, but instead provided
     by a Solver.
   */
  class AbsSort
  {
  public:
    AbsSort(Type t) : type(t) {};
    virtual ~AbsSort() {};
    virtual std::string to_string() const = 0;
    bool is_array() const { return type == ARRAY; };
    bool is_bool() const { return type == BOOL; };
    bool is_bv() const { return type == BV; };
    bool is_int() const { return type == INT; };
    bool is_real() const { return type == REAL; };
    // TODO: decide on exception or special value for incorrect usage
    virtual unsigned int get_width() const = 0;
    virtual unsigned int get_indexsort() const = 0;
    virtual unsigned int get_elemsort() const = 0;
    Type get_type() const { return type; };
  protected:
    Type type;
  };

}

#endif
