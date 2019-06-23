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

TEST := bats ${EXERCISE}/$(subst -,_,${EXERCISE})_test.sh

test:
	${TEST}
.PHONY: test

dev:
	find . -name "*.sh" | entr -c ${TEST}
.PHONY: dev
