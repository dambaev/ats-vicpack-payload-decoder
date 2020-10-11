all:
	make -C src

tests:
	make tests -C src

install:
	make install -C src

clean:
	make -C src clean


