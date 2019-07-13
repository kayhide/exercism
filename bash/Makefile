EXERCISMS := $(shell find . -name ".exercism")
EXERCISES := $(EXERCISMS:./%/.exercism=%)
SRCS := $(foreach ex,${EXERCISES},${ex}/$(subst -,_,${ex}).sh)
MAKEFILES := $(foreach ex,${EXERCISES},${ex}/Makefile)


init: ${SRCS} ${MAKEFILES}
.PHONY: init

%.sh:
	cp hello-world/hello_world.sh $@

%/Makefile:
	@echo "EXERCISE := ${@D}" > $@
	@echo "" >> $@
	@echo "include ../Makefile" >> $@


# Exercise Commands

SRC := $(subst -,_,${EXERCISE}).sh
TEST := $(subst -,_,${EXERCISE})_test.sh

test:
	bats ${TEST} && shellcheck ${SRC}
.PHONY: test

dev:
	find . -name "*.sh" | entr -c bash -c "timeout 3 bats -t ${TEST} && shellcheck ${SRC}"
.PHONY: dev
