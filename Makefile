.PHONY: all paper checks lean lint format
PYTHON ?= python3

all: lint checks lean paper

paper:
	./paper/build.sh
	$(PYTHON) -I tools/check_paper.py

checks:
	mkdir -p work
	$(PYTHON) checks/research_checks.py work/research-results.json > /dev/null
	$(PYTHON) -I tools/compare_results.py checks/research-results.json work/research-results.json

lean:
	cd formalization && $(PYTHON) verify.py

lint:
	$(PYTHON) -m ruff check .
	$(PYTHON) -m ruff format --check .
	cffconvert --validate

format:
	$(PYTHON) -m ruff check --fix .
	$(PYTHON) -m ruff format .
