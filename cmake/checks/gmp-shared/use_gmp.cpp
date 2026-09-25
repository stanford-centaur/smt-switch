// Touches enough of GMP that the linker has to pull objects out of a static
// archive, which is what makes a non position independent one fail here.
#include <gmp.h>

extern "C" void smt_switch_probe_gmp()
{
  mpz_t value;
  mpz_init_set_ui(value, 1);
  mpz_mul_ui(value, value, 2);
  mpz_clear(value);
}
