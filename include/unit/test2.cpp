#include <iostream>
#include <memory>
#include <string>

class A
{
public:
  virtual std::string who() const = 0;
};

class B : public A
{
public:
  B() {};
  std::string who() const override { return "I am B"; };
};

std::shared_ptr<B> create_b()
{
  std::shared_ptr<B> bp(new B());
  return bp;
}

using namespace std;
int main()
{
  shared_ptr<A> ap = create_b();
  cout << ap->who() << endl;
}
