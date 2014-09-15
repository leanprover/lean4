CASK ?= cask
EMACS ?= emacs

all: test

test: unit ecukes

unit:
	${CASK} exec ert-runner

ecukes:
	${CASK} exec ecukes

install:
	${CASK} install

.PHONY:	all test unit ecukes install
