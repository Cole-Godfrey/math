.PHONY: fetch verify test check

fetch:
	python3 -m repository fetch

verify:
	python3 -m repository verify --clean

test: fetch
	python3 -m unittest discover -s tests -v

check: test
