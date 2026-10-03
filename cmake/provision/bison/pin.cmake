# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default.
smt_switch_pin(
  BISON
  GNU_PROJECT bison
  VERSION 3.8.2
  CHECKSUM 06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb
)
