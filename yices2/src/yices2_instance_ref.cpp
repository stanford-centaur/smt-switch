/*!
 * \file yices2_instance_ref.cpp
 * \brief Counts the references to the Yices instance, setting it up for the
 *        first and freeing it after the last.
 * \author Áron Ricardo Perez-Lopez
 * \date 2026
 * \copyright See the LICENSE file in the top-level source directory.
 */

#include "yices2_instance_ref.h"

#include <yices.h>

#include <cstddef>
#include <mutex>

namespace smt {

namespace {

// locked around every count change, including the yices_init() and
// yices_exit() calls, so no thread sees Yices half set up
std::mutex count_mutex;
std::size_t count = 0;

void acquire()
{
  std::lock_guard lock(count_mutex);
  if (count++ == 0)
  {
    yices_init();
  }
}

}  // namespace

Yices2InstanceRef::Yices2InstanceRef() { acquire(); }

Yices2InstanceRef::Yices2InstanceRef(const Yices2InstanceRef &) { acquire(); }

Yices2InstanceRef::~Yices2InstanceRef()
{
  std::lock_guard lock(count_mutex);
  if (--count == 0)
  {
    yices_exit();
  }
}

}  // namespace smt
