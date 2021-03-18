all: cvc4_qf_ufbv btor_qf_ufbv

# Note: assumes smt-switch has been installed in a directory called
# example-install in this directory

cvc4_qf_ufbv: cvc4_qf_ufbv.cpp
	$(CXX) -std=c++11 -I./example-install/include -L./example-install/lib -Wl,-rpath,./example-install/lib cvc4_qf_ufbv.cpp -o cvc4_qf_ufbv.out -lsmt-switch-cvc4 -lsmt-switch

btor_qf_ufbv: btor_qf_ufbv.cpp
	$(CXX) -std=c++11 -I./example-install/include -L./example-install/lib -Wl,-rpath,./example-install/lib btor_qf_ufbv.cpp -o btor_qf_ufbv.out -lsmt-switch-btor -lsmt-switch

clean:
	rm -rf cvc4_qf_ufbv.out btor_qf_ufbv.out
