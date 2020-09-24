###############################################################
# \file available_solvers.py
# \verbatim
# Top contributors (to current version):
#   Makai Mann
# This file is part of the smt-switch project.
# Copyright (c) 2020 by the authors listed in the file AUTHORS
# in the top-level source directory) and their institutional affiliations.
# All rights reserved.  See the file LICENSE in the top-level source
# directory for licensing information.\endverbatim
#
# \brief
#
#
#

import smt_switch as ss


termiter_support_solvers = {k:v for k, v in ss.solvers.items() if k != 'yices2'}
int_support_solvers      = {k:v for k, v in ss.solvers.items() if k != 'btor'}
