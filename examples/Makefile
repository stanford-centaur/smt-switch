all: cvc5_qf_ufbv btor_qf_ufbv

# Note: assumes smt-switch has been installed in a directory called
# example-install in this directory, which is automated by build.sh

cvc5_qf_ufbv: cvc5_qf_ufbv.cpp
	$(CXX) -std=c++11 -I./example-install/include -L./example-install/lib -Wl,-rpath,./example-install/lib cvc5_qf_ufbv.cpp -o cvc5_qf_ufbv.out -lsmt-switch-cvc5 -lsmt-switch

btor_qf_ufbv: btor_qf_ufbv.cpp
	$(CXX) -std=c++11 -I./example-install/include -L./example-install/lib -Wl,-rpath,./example-install/lib btor_qf_ufbv.cpp -o btor_qf_ufbv.out -lsmt-switch-btor -lsmt-switch

clean:
	rm -rf cvc5_qf_ufbv.out btor_qf_ufbv.out

clean-all: clean
	rm -rf ./example-build ./example-install
