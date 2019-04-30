#include <array>
#include <iostream>

using namespace std;

constexpr array<string_view, 2> gen_constexpr_array()
{
  array<string_view, 2> sv_array;
  sv_array[0] = string_view("constant_string1");
  sv_array[1] = string_view("constant_string2");
  return sv_array;
}

int main()
{
  constexpr array<string_view, 2> sv_array = gen_constexpr_array();
  static_assert(sv_array[0] == string_view("constant_string1"));
  static_assert(sv_array[1] == "constant_string2");
  cout << sv_array[0] << endl;
  cout << sv_array[1] << endl;
  // string_view sv = "constant string";
  // cout << sv << endl;
}
