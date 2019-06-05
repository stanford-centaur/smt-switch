#include "sort.h"

namespace smt {

std::string to_string(Kind k) { return std::string(kind2str[k]); }

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

bool operator==(const Sort & s1, const Sort & s2) { return s1->compare(s2); }

std::ostream & operator<<(std::ostream & output, const Sort s)
{
  output << s->to_string();
  return output;
}

}  // namespace smt
