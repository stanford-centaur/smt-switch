#pragma once

#include <memory>

#include "assert.h"

// determine if my_ptr is just an alias for shared_ptr
#define USE_SHARED_PTR

namespace smt {

#ifdef USE_SHARED_PTR

template <typename _Tp>
using my_ptr = std::shared_ptr<_Tp>;

#else

struct nop
{
  template <typename T>
  void operator()(T const &) const noexcept
  {
  }
};

/// adapted 20.7.12.2 unique_ptr for single objects.
/// to my_ptr with a nop deleter and no deleted copiers

template <typename _Tp, typename _Tp_Deleter = nop>
class my_ptr
{
  typedef std::tuple<_Tp *, _Tp_Deleter> __tuple_type;
  typedef __tuple_type my_ptr::*__unspecified_bool_type;
  typedef _Tp * my_ptr::*__unspecified_pointer_type;

 public:
  typedef _Tp * pointer;
  typedef _Tp element_type;
  typedef _Tp_Deleter deleter_type;

  // Constructors.
  my_ptr() : _M_t(pointer(), deleter_type())
  {
    static_assert(!std::is_pointer<deleter_type>::value,
                  "constructed with null function pointer deleter");
  }

  explicit my_ptr(pointer __p) : _M_t(__p, deleter_type())
  {
    static_assert(!std::is_pointer<deleter_type>::value,
                  "constructed with null function pointer deleter");
  }

  my_ptr(pointer __p,
         typename std::conditional<std::is_reference<deleter_type>::value,
                                   deleter_type,
                                   const deleter_type &>::type __d)
      : _M_t(__p, __d)
  {
  }

  my_ptr(pointer __p, typename std::remove_reference<deleter_type>::type && __d)
      : _M_t(std::move(__p), std::move(__d))
  {
    static_assert(!std::is_reference<deleter_type>::value,
                  "rvalue deleter bound to reference");
  }

  // Destructor.
  ~my_ptr() { reset(); }

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

  pointer get() const { return std::get<0>(_M_t); }

  typename std::add_lvalue_reference<deleter_type>::type get_deleter()
  {
    return std::get<1>(_M_t);
  }

  typename std::add_lvalue_reference<
      typename std::add_const<deleter_type>::type>::type
  get_deleter() const
  {
    return std::get<1>(_M_t);
  }

  operator __unspecified_bool_type() const
  {
    return get() == 0 ? 0 : &my_ptr::_M_t;
  }

  // Modifiers.
  pointer release()
  {
    pointer __p = get();
    std::get<0>(_M_t) = 0;
    return __p;
  }

  void reset(pointer __p = pointer())
  {
    if (__p != get())
    {
      get_deleter()(get());
      std::get<0>(_M_t) = __p;
    }
  }

  void swap(my_ptr && __u)
  {
    using std::swap;
    swap(_M_t, __u._M_t);
  }

 private:
  __tuple_type _M_t;
};
#endif
}  // namespace smt
