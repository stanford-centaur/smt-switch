# SPDX-FileCopyrightText: 2020 the smt-switch authors
# SPDX-FileContributor: Amalee Wilson
# SPDX-License-Identifier: BSD-3-Clause

import smt_switch as ss

termiter_support_solvers = {k: v for k, v in ss.solvers.items() if k != "yices2"}
int_support_solvers = {
    k: v for k, v in ss.solvers.items() if k not in {"btor", "bitwuzla"}
}
