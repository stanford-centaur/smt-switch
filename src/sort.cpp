#include "sort.h"

namespace smt {

/**
   This function should only be called once, to generate the constexpr
   kind2str for converting enums to string_views.
*/
constexpr std::array<std::string_view, NUM_KINDS> generate_kind2str()
{
  std::array<std::string_view, NUM_KINDS> kind2str;

  kind2str[ARRAY] = std::string_view("ARRAY");
  kind2str[BOOL] = std::string_view("BOOL");
  kind2str[BV] = std::string_view("BV");
  kind2str[INT] = std::string_view("INT");
  kind2str[REAL] = std::string_view("REAL");
  kind2str[UNINTERPRETED] = std::string_view("UNINTERPRETED");

  return kind2str;
}

constexpr std::array<std::string_view, NUM_KINDS> kind2str =
    generate_kind2str();

std::string to_string(Kind k) { return std::string(kind2str[k]); }

/* AbsSort implementation */
std::string AbsSort::to_string() const
{
  if ((kind != BV) && (kind != ARRAY))
  {
    return ::smt::to_string(kind);
  }
  else
  {
    std::ostringstream oss;
    if (kind == BV)
    {
      oss << "BV{" << get_width() << "}";
    }
    else if (kind == ARRAY)
    {
      oss << "ARRAY{" << get_indexsort()->to_string() << ", "
          << get_elemsort()->to_string() << "}";
    }
    else
    {
      Unreachable();
    }
    return oss.str();
  }
};
/* end AbsSort implementation */

bool operator==(const Sort & s1, const Sort & s2) { return s1->compare(s2); }

std::ostream & operator<<(std::ostream & output, const Sort s)
{
  output << s->to_string();
  return output;
}

}  // namespace smt
