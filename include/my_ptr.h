#pragma once

#include <memory>

#include "assert.h"

// determine if my_ptr is just an alias for shared_ptr
//#define USE_SHARED_PTR

namespace smt {

#ifdef USE_SHARED_PTR

template <typename _Tp>
using my_ptr = std::shared_ptr<_Tp>;

#else

/// adapted 20.7.12.2 unique_ptr for single objects.
/// to my_ptr with a nop deleter and no deleted copiers

template <typename _Tp>
class my_ptr
{
  typedef _Tp * my_ptr::*__unspecified_bool_type;
  typedef _Tp * my_ptr::*__unspecified_pointer_type;

 public:
  typedef _Tp * pointer;
  typedef _Tp element_type;

  // Constructors.
  my_ptr() : _raw_ptr(pointer()) {}

  explicit my_ptr(pointer __p) : _raw_ptr(__p) {}

  // Destructor.
  ~my_ptr() {}

  // Assignment.

  my_ptr & operator=(__unspecified_pointer_type)
  {
    reset();
    return *this;
  }

  // Observers.
  typename std::add_lvalue_reference<element_type>::type operator*() const
  {
    assert(get() != 0);
    return *get();
  }

  pointer operator->() const
  {
    assert(get() != 0);
    return get();
  }

  pointer get() const { return _raw_ptr; }

  operator __unspecified_bool_type() const
  {
    return get() == 0 ? 0 : &my_ptr::_raw_ptr;
  }

  // Modifiers.
  pointer release()
  {
    pointer __p = get();
    _raw_ptr = 0;
    return __p;
  }

  void reset(pointer __p = pointer())
  {
    if (__p != get())
    {
      _raw_ptr = __p;
    }
  }

  void swap(my_ptr && __u)
  {
    using std::swap;
    swap(_raw_ptr, __u._raw_ptr);
  }

  template <typename _Tp1,
            typename = typename std::enable_if<
                std::is_convertible<_Tp1 *, _Tp *>::value>::type>
  my_ptr(const my_ptr<_Tp1> & u) : _raw_ptr((pointer)u._raw_ptr)
  {
  }

  template <typename _Tp1,
            typename = typename std::enable_if<
                std::is_convertible<_Tp1 *, _Tp *>::value>::type>
  my_ptr & operator=(my_ptr<_Tp1> u)
  {
    _raw_ptr = (pointer)u._raw_ptr;
    return *this;
  }

 private:
  pointer _raw_ptr;

  template <typename _Tp1>
  friend class my_ptr;
};

#endif
}  // namespace smt

#ifndef USE_SHARED_PTR
namespace std {
template <typename _Tp, typename _Tp1>
inline smt::my_ptr<_Tp> static_pointer_cast(const smt::my_ptr<_Tp1> & __r)
{
  return smt::my_ptr<_Tp>(static_cast<_Tp *>(__r.get()));
}

}  // namespace std
#endif
