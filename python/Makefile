all: smt_switch

smt_switch: setup-smt_switch.py smt_switch.pyx ops.pxd
	python setup-smt_switch.py build_ext --inplace

clean:
	rm -f smt_switch.cpp smt_switch.cpython-*
	rm -rf build
